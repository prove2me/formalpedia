-- Prove2me | Theorems.Thm_DeltaSLearning_eq_23
-- name    : DeltaSLearning.eq_23
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:12:00.550658+00:00
-- url     : https://prove2.me/theorems/159e54b3-8a56-4c6f-9dba-d1a470e9b592
-- title:
--   Eq. (23) — $R_N\le2(1+6\rho\beta)\,\mathbb E[\sum_n(V(\delta^n,S^n)-V^*)]+c\beta+K$
-- statement:
--   Run the $(\delta,S)$ learning algorithm with any $J\ge1$, any step sizes, any nonnegative confidence sizes and any initial targets $S^1_j\in[\delta_j,\beta]$. For every number of epochs $N$,
--   $$R_N\le 2(1+6\rho\beta)\,\mathbb E\Bigl[\sum_{n=1}^N\bigl(V(\delta^n,S^n)-V^*\bigr)\Bigr]+c\beta+K,$$
--   where $\delta^n=\delta_{j^n}$ and $S^n=\max(x^n,S^n_{j^n})$ are the gap and target the algorithm implements in epoch $n$, and the sum is integrable.
--
--   This reduces the regret to the per-epoch optimality gaps of the implemented policies, which (25) splits into four losses (Propositions 1–4).
--
--   Differences from the source:
--   - generalization: derived for Theorem 3's parameters J = ⌊√N⌋, ηⁿ, Δⁿ → any J ≥ 1, any step sizes, any confidence sizes Δⁿ ≥ 0; reason: the derivation of (23)–(24) uses none of the parameter choices; Theorem 3's Δⁿ are positive, so this specializes to the source
--   - reading: R_N, the regret over N epochs (Definition 2 is per period against π*; (23) writes "− TV*") → E[Σ_{t ≤ T_N} C̃_t] − V*·E[T_N], with C̃_t the pseudo cost (7) the algorithm incurs and T_N the last period of epoch N; reason: Theorem 3 indexes regret by epochs; pseudo costs differ from costs by p·d_t, which no policy affects, so with E[D] < ∞ this is the true-cost regret against T_N·V*
--   - reading: V* := V(δ*, S*) for the clairvoyant optimal (δ*, S*) policy of Theorem 1, with S* ≤ β; (9) and Table 3 write V* = min_{δ,S} V(δ, S) → V* = sInf of V(δ, S) = E[G]/E[L] over 0 ≤ δ ≤ S ≤ β; reason: Theorem 1 (Zheng 1991) is cited, not formalized; the paper's analysis (Theorem 2, Proposition 1) works on 0 ≤ δ ≤ S ≤ β. If never ordering (s < 0) were the clairvoyant optimum, V(δ*, S*) would be undefined, so the paper's V* is read as this minimum; the set is nonempty and bounded (|V| ≤ γ)
--   - reading: epoch n implements (δⁿ, Sⁿ) = (δ_{jⁿ}, max(xⁿ, Sⁿ_{jⁿ})) (14), runs while the epoch's sales ≤ δ̄ⁿ and completes the current cycle (Algorithm 1) → first period orders up to Sⁿ, later periods use the (δⁿ, Sⁿ) rule; the while-loop ends at the first period whose cumulative sales exceed δ̄ⁿ; the epoch ends at the first later period ending with inventory ≤ Sⁿ − δⁿ; reason: the proof's "forced to take xⁿ⁺¹ instead" (p.26) and the term c(Sⁿ⁺¹ − Sⁿ) (p.19); "keep running (δⁿ,Sⁿ) policy until inventory drops below Sⁿ − δⁿ" (Algorithm 1)
--   - reading: jⁿ := argmax_{j ∈ 𝒜ⁿ} Sⁿ_j (13), no tie-break → smallest maximizing index; reason: the proof uses only jⁿ ∈ 𝒜ⁿ and Sⁿ_{jⁿ} = max_{j ∈ 𝒜ⁿ} Sⁿ_j
--   - reading: c and h are per-unit ordering and holding costs, sign not stated (p.7) → c ≥ 0 and h > 0; reason: costs are nonnegative; (19) divides by h, and for c < 0 the bound γ of (10) can be negative, so Lemma 1 would fail
--   - reading: i.i.d. continuous demands whose pdf satisfies f(d) ≤ ρ for d ≥ 0 (Assumption 1) → D t measurable, iIndepFun, IdentDistrib to D 0, and the law of D 0 is ≤ ρ·Lebesgue on [0, ∞); reason: demands are nonnegative quantities (Lemma 2 and the proof of Lemma 3: "D is positive"); the measure inequality is exactly a Lebesgue density bounded by ρ and supported on [0, ∞)
--   - encoding: periods t = 1, 2, … → 0-based: D t is the demand of period t + 1; reason: Lean indexing; no instance changes
--   - encoding: E[Σ_n (V(δⁿ, Sⁿ) − V*)] (finiteness presupposed) → integrability of Σ_n (V(δⁿ, Sⁿ) − V*) stated as an extra conclusion; reason: Bochner integrals are 0 on non-integrable functions; the conclusion rules out that junk reading and holds because the expectation is finite
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (23), p.19, with (24), pp.19–20

import Mathlib
import Definitions.Def_DeltaSLearning_IsDemandProcess
import Definitions.Def_DeltaSLearning_regret

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **The regret reduction (23).** For the `(δ, S)` learning algorithm with any `J ≥ 1`, any
step sizes `η`, any nonnegative confidence sizes `Δ` and any initial targets
`S¹_j ∈ [δ_j, β]`, and every number of epochs `N`,
`R_N ≤ 2(1 + 6ρβ) E[Σ_{n=1}^N (V(δⁿ, Sⁿ) - V*)] + cβ + K`,
where `δⁿ = δ_{jⁿ}` and `Sⁿ = max(xⁿ, Sⁿ_{jⁿ})` are the gap and target implemented in epoch `n`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (23), p.19, with (24), pp.19–20.

**Formalization Note** The page derives (23) for Theorem 3's parameters; the derivation uses none
of them, so it is stated for general `J ≥ 1`, `η` and `Δ ≥ 0` (`Δ ≥ 0` keeps the active set
nonempty). `R_N` is `regret` (pseudo costs actually incurred, benchmark `T_N V*`); epoch `n + 1`
uses the state `algState … n`. Integrability of the epoch sum is stated as a conclusion. -/
theorem eq_23 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (cp : Params) (hD : IsDemandProcess P D cp.ρ) (N J : ℕ) (hJ : 1 ≤ J)
    (η Δ : ℕ → ℝ) (hΔ : ∀ n, 0 ≤ Δ n) (S₁ : ℕ → ℝ)
    (hS₁ : ∀ j ∈ Finset.Icc 1 J, S₁ j ∈ Set.Icc (grid cp.β J j) cp.β) :
    let σ : Ω → ℕ → AlgState := fun ω n => algState cp J η Δ S₁ (fun t => D t ω) n
    Integrable (fun ω => ∑ n ∈ Finset.range N,
        (avgCost P D cp (grid cp.β J (leader (σ ω n))) (max (σ ω n).x ((σ ω n).S (leader (σ ω n))))
          - optAvgCost P D cp)) P ∧
      regret P D cp J η Δ S₁ N ≤
        2 * (1 + 6 * cp.ρ * cp.β) *
            ∫ ω, ∑ n ∈ Finset.range N,
              (avgCost P D cp (grid cp.β J (leader (σ ω n)))
                  (max (σ ω n).x ((σ ω n).S (leader (σ ω n)))) - optAvgCost P D cp) ∂P
          + cp.c * cp.β + cp.K := by sorry

end DeltaSLearning
