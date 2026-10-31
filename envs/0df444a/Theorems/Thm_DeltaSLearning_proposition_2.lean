-- Prove2me | Theorems.Thm_DeltaSLearning_proposition_2
-- name    : DeltaSLearning.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:11:39.145344+00:00
-- url     : https://prove2.me/theorems/d7fc57b6-e6b2-40bb-a63d-c01fa2b0f427
-- title:
--   Proposition 2 — pruning loss $\mathbb E[\sum_n(V^*_{j^n}-V^*_{j^*})]=O(\log N\sqrt N)$
-- statement:
--   Assume Assumption 1 and the cost parameters of §2, and run the $(\delta,S)$ learning algorithm with Theorem 3's parameters $J=\lfloor\sqrt N\rfloor$, $\eta^n=\beta/(\xi\sqrt n)$, $\Delta^n=2\theta\log(8N^2)/\sqrt n$. There is a constant $C$ such that for every $N\ge2$ and every initialization $S^1_j\in[\delta_j,\beta]$,
--   $$\mathbb E\Bigl[\sum_{n=1}^N\bigl(V^*_{j^n}-V^*_{j^*}\bigr)\Bigr]\le C\log N\sqrt N,$$
--   where $V^*_{j^n}=V^*(\delta^n)$ and $V^*_{j^*}=\min_{j\in[J]}V^*(\delta_j)$; the sum is integrable.
--
--   This is the third term of (25), the cost of the bandit-style pruning of the gaps.
--
--   Differences from the source:
--   - reading: = O(log N √N) → ∃ C, ∀ N ≥ 2, ∀ initial targets S¹_j ∈ [δ_j, β]: bound ≤ C·log N √N; reason: C may depend on the instance but not on N or on the arbitrary initialization (p.13); N = 1 is excluded only because log 1 = 0
--   - encoding: V*_{j*} with j* = argmin_j V*_j → sInf of the finite nonempty set {V*(δ_j) : j ∈ [J]}; reason: the minimum of a finite nonempty set
--   - reading: epoch n implements (δⁿ, Sⁿ) = (δ_{jⁿ}, max(xⁿ, Sⁿ_{jⁿ})) (14), runs while the epoch's sales ≤ δ̄ⁿ and completes the current cycle (Algorithm 1) → first period orders up to Sⁿ, later periods use the (δⁿ, Sⁿ) rule; the while-loop ends at the first period whose cumulative sales exceed δ̄ⁿ; the epoch ends at the first later period ending with inventory ≤ Sⁿ − δⁿ; reason: the proof's "forced to take xⁿ⁺¹ instead" (p.26) and the term c(Sⁿ⁺¹ − Sⁿ) (p.19); "keep running (δⁿ,Sⁿ) policy until inventory drops below Sⁿ − δⁿ" (Algorithm 1)
--   - reading: jⁿ := argmax_{j ∈ 𝒜ⁿ} Sⁿ_j (13), no tie-break → smallest maximizing index; reason: the proof uses only jⁿ ∈ 𝒜ⁿ and Sⁿ_{jⁿ} = max_{j ∈ 𝒜ⁿ} Sⁿ_j
--   - reading: c and h are per-unit ordering and holding costs, sign not stated (p.7) → c ≥ 0 and h > 0; reason: costs are nonnegative; (19) divides by h, and for c < 0 the bound γ of (10) can be negative, so Lemma 1 would fail
--   - reading: i.i.d. continuous demands whose pdf satisfies f(d) ≤ ρ for d ≥ 0 (Assumption 1) → D t measurable, iIndepFun, IdentDistrib to D 0, and the law of D 0 is ≤ ρ·Lebesgue on [0, ∞); reason: demands are nonnegative quantities (Lemma 2 and the proof of Lemma 3: "D is positive"); the measure inequality is exactly a Lebesgue density bounded by ρ and supported on [0, ∞)
--   - encoding: periods t = 1, 2, … → 0-based: D t is the demand of period t + 1; reason: Lean indexing; no instance changes
--   - encoding: E[Σ_n (V*_{jⁿ} − V*_{j*})] (finiteness presupposed) → integrability of Σ_n (V*_{jⁿ} − V*_{j*}) stated as an extra conclusion; reason: Bochner integrals are 0 on non-integrable functions; the conclusion rules out that junk reading and holds because the expectation is finite
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Proposition 2, eq. (27), p.21; proof pp.24–25

import Mathlib
import Definitions.Def_DeltaSLearning_IsDemandProcess
import Definitions.Def_DeltaSLearning_algState__6eb4c5
import Definitions.Def_DeltaSLearning_optAvgCostGap
import Definitions.Def_DeltaSLearning_stepSize
import Definitions.Def_DeltaSLearning_confSize

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Proposition 2** (pruning loss bound). With Theorem 3's parameters `J = ⌊√N⌋`,
`ηⁿ = β/(ξ√n)`, `Δⁿ = 2θ log(8N²)/√n`,
`E[Σ_{n=1}^N (V*_{jⁿ} - V*_{j*})] = O(log N √N)`, uniformly in the initial targets
`S¹_j ∈ [δ_j, β]`; here `V*_{jⁿ} = V*(δⁿ)` and `V*_{j*} = min_{j ∈ [J]} V*(δ_j)`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Proposition 2 and eq. (27), p.21; proof pp.24–25.

**Formalization Note** The `O(·)` is read as `∃ C ∀ N ≥ 2 ∀ S¹`. Epoch `n + 1` uses the state
`algState … n`. Integrability of the sum is stated as a conclusion. -/
theorem proposition_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (cp : Params) (hD : IsDemandProcess P D cp.ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ S₁ : ℕ → ℝ,
      (∀ j ∈ Finset.Icc 1 ⌊Real.sqrt N⌋₊, S₁ j ∈ Set.Icc (grid cp.β ⌊Real.sqrt N⌋₊ j) cp.β) →
      let J := ⌊Real.sqrt N⌋₊
      let σ : Ω → ℕ → AlgState := fun ω n =>
        algState cp J (stepSize cp) (confSize cp N) S₁ (fun t => D t ω) n
      let best := sInf ((fun j => optAvgCostGap P D cp (grid cp.β J j)) '' Set.Icc 1 J)
      Integrable (fun ω => ∑ n ∈ Finset.range N,
          (optAvgCostGap P D cp (grid cp.β J (leader (σ ω n))) - best)) P ∧
        ∫ ω, ∑ n ∈ Finset.range N, (optAvgCostGap P D cp (grid cp.β J (leader (σ ω n))) - best) ∂P
          ≤ C * Real.log N * Real.sqrt N := by sorry

end DeltaSLearning
