-- Prove2me | Theorems.Thm_DeltaSLearning_theorem_3
-- name    : DeltaSLearning.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:11:51.158988+00:00
-- url     : https://prove2.me/theorems/1e043bea-3b6c-40b0-b4cd-4679a5e6b0eb
-- title:
--   Theorem 3 — the $(\delta,S)$ learning algorithm has regret $O(\log N\sqrt N)$
-- statement:
--   Consider the periodic-review lost-sales inventory system with fixed ordering cost $K>0$, unit costs $c\ge0$, $h>0$, $p>c$, capacity $\beta\ge0$, and i.i.d. demands whose density is bounded by $\rho$ (Assumption 1). Run the $(\delta,S)$ learning algorithm for $N$ epochs with
--   $$J=\lfloor\sqrt N\rfloor,\qquad \eta^n=\frac{\beta}{\xi\sqrt n},\qquad \Delta^n=\frac{2\theta\log(8N^2)}{\sqrt n},$$
--   where $\xi=\nu/\sqrt2$, $\theta=(2\gamma+4)\max(\nu,b)+1.5\beta\xi$, $\nu=4\gamma\sqrt{\exp((12\beta\rho p+2p)/h)}$, $b=2\gamma$ and $\gamma=K+(h+c+p)\beta$. Then $R_N=O(\log N\sqrt N)$: there is a constant $C$ such that for every $N\ge2$ and every initialization $S^1_j\in[\delta_j,\beta]$, the total pseudo cost and the number of periods $T_N$ are integrable and
--   $$R_N=\mathbb E\Bigl[\sum_{t=1}^{T_N}\tilde C_t\Bigr]-V^*\,\mathbb E[T_N]\le C\log N\sqrt N .$$
--
--   Since $N\le T_N$, this is an $O(\log T\sqrt T)$ regret, which matches the $\Omega(\sqrt T)$ lower bound for the repeated newsvendor problem up to the logarithm. It is the first regret bound for learning in an inventory system with fixed costs.
--
--   Differences from the source:
--   - reading: R_N, the regret over N epochs (Definition 2 is per period against π*; (23) writes "− TV*") → E[Σ_{t ≤ T_N} C̃_t] − V*·E[T_N], with C̃_t the pseudo cost (7) the algorithm incurs and T_N the last period of epoch N; reason: Theorem 3 indexes regret by epochs; pseudo costs differ from costs by p·d_t, which no policy affects, so with E[D] < ∞ this is the true-cost regret against T_N·V*
--   - reading: V* := V(δ*, S*) for the clairvoyant optimal (δ*, S*) policy of Theorem 1, with S* ≤ β; (9) and Table 3 write V* = min_{δ,S} V(δ, S) → V* = sInf of V(δ, S) = E[G]/E[L] over 0 ≤ δ ≤ S ≤ β; reason: Theorem 1 (Zheng 1991) is cited, not formalized; the paper's analysis (Theorem 2, Proposition 1) works on 0 ≤ δ ≤ S ≤ β. If never ordering (s < 0) were the clairvoyant optimum, V(δ*, S*) would be undefined, so the paper's V* is read as this minimum; the set is nonempty and bounded (|V| ≤ γ)
--   - reading: = O(log N √N) → ∃ C, ∀ N ≥ 2, ∀ initial targets S¹_j ∈ [δ_j, β]: bound ≤ C·log N √N; reason: C may depend on the instance but not on N or on the arbitrary initialization (p.13); N = 1 is excluded only because log 1 = 0
--   - reading: epoch n implements (δⁿ, Sⁿ) = (δ_{jⁿ}, max(xⁿ, Sⁿ_{jⁿ})) (14), runs while the epoch's sales ≤ δ̄ⁿ and completes the current cycle (Algorithm 1) → first period orders up to Sⁿ, later periods use the (δⁿ, Sⁿ) rule; the while-loop ends at the first period whose cumulative sales exceed δ̄ⁿ; the epoch ends at the first later period ending with inventory ≤ Sⁿ − δⁿ; reason: the proof's "forced to take xⁿ⁺¹ instead" (p.26) and the term c(Sⁿ⁺¹ − Sⁿ) (p.19); "keep running (δⁿ,Sⁿ) policy until inventory drops below Sⁿ − δⁿ" (Algorithm 1)
--   - reading: jⁿ := argmax_{j ∈ 𝒜ⁿ} Sⁿ_j (13), no tie-break → smallest maximizing index; reason: the proof uses only jⁿ ∈ 𝒜ⁿ and Sⁿ_{jⁿ} = max_{j ∈ 𝒜ⁿ} Sⁿ_j
--   - reading: c and h are per-unit ordering and holding costs, sign not stated (p.7) → c ≥ 0 and h > 0; reason: costs are nonnegative; (19) divides by h, and for c < 0 the bound γ of (10) can be negative, so Lemma 1 would fail
--   - reading: i.i.d. continuous demands whose pdf satisfies f(d) ≤ ρ for d ≥ 0 (Assumption 1) → D t measurable, iIndepFun, IdentDistrib to D 0, and the law of D 0 is ≤ ρ·Lebesgue on [0, ∞); reason: demands are nonnegative quantities (Lemma 2 and the proof of Lemma 3: "D is positive"); the measure inequality is exactly a Lebesgue density bounded by ρ and supported on [0, ∞)
--   - encoding: periods t = 1, 2, … → 0-based: D t is the demand of period t + 1; reason: Lean indexing; no instance changes
--   - encoding: E[the total pseudo cost and of T_N] (finiteness presupposed) → integrability of the total pseudo cost and of T_N stated as an extra conclusion; reason: Bochner integrals are 0 on non-integrable functions; the conclusion rules out that junk reading and holds because the expectation is finite
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 3, eqs. (18)–(19), p.17

import Mathlib
import Definitions.Def_DeltaSLearning_IsDemandProcess
import Definitions.Def_DeltaSLearning_regret
import Definitions.Def_DeltaSLearning_stepSize
import Definitions.Def_DeltaSLearning_confSize

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Theorem 3** (regret bound). For the periodic-review lost-sales inventory system with fixed
cost `K > 0`, unit costs `c ≥ 0`, `h > 0`, `p > c`, capacity `β ≥ 0` and i.i.d. demands with a
density bounded by `ρ` (Assumption 1), run the `(δ, S)` learning algorithm for `N` epochs with
`J = ⌊√N⌋`, `ηⁿ = β/(ξ√n)` and `Δⁿ = 2θ log(8N²)/√n`, `ξ`, `θ` from (18)–(19). Then
`R_N = O(log N √N)`: there is a constant `C` such that for every `N ≥ 2` and every initialization
`S¹_j ∈ [δ_j, β]`, the total pseudo cost and the number of periods `T_N` are integrable and
`R_N ≤ C log N √N`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 3 and eqs. (18)–(19), p.17.

**Formalization Note** (a) `R_N` is `regret`: `E[Σ_{t ≤ T_N} C̃_t] - V* E[T_N]`, pseudo costs
actually incurred against the benchmark `T_N V*` of (23); `V*` is the infimum of `V` over
`0 ≤ δ ≤ S ≤ β`. (b) `C` may depend on the instance (`K, c, h, p, β, ρ` and the demand law) but
not on `N` or the initialization; `N = 1` is excluded only because `log 1 = 0`. (c) The
algorithm is `algState`: epoch start by ordering up to `max(xⁿ, Sⁿ_{jⁿ})`, while-loop on sales,
cycle completion, simulation from sales, smallest-index tie-break. (d) Integrability is a
conclusion, never a hypothesis. -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (cp : Params) (hD : IsDemandProcess P D cp.ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ S₁ : ℕ → ℝ,
      (∀ j ∈ Finset.Icc 1 ⌊Real.sqrt N⌋₊, S₁ j ∈ Set.Icc (grid cp.β ⌊Real.sqrt N⌋₊ j) cp.β) →
      Integrable (fun ω =>
          (algState cp ⌊Real.sqrt N⌋₊ (stepSize cp) (confSize cp N) S₁ (fun t => D t ω) N).cost) P ∧
        Integrable (fun ω =>
          ((algState cp ⌊Real.sqrt N⌋₊ (stepSize cp) (confSize cp N) S₁ (fun t => D t ω) N).t : ℝ))
          P ∧
        regret P D cp ⌊Real.sqrt N⌋₊ (stepSize cp) (confSize cp N) S₁ N
          ≤ C * Real.log N * Real.sqrt N := by sorry

end DeltaSLearning
