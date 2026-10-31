-- Prove2me | Theorems.Thm_DeltaSLearning_proposition_1
-- name    : DeltaSLearning.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:09:27.353462+00:00
-- url     : https://prove2.me/theorems/dfe523e5-0206-42aa-a174-09ecf067ea14
-- title:
--   Proposition 1 — discretization loss $N(V^*_{j^*}-V^*)=O(\sqrt N)$
-- statement:
--   Assume Assumption 1 and the cost parameters of §2. With $J=\lfloor\sqrt N\rfloor$ and the grid $\delta_j=j\beta/J$, let $V^*_{j^*}=\min_{j\in[J]}V^*(\delta_j)$ be the best value on the grid. There is a constant $C$ such that for every $N\ge1$
--   $$N\bigl(V^*_{j^*}-V^*\bigr)\le C\sqrt N .$$
--
--   This is the fourth term of the decomposition (25); no algorithm is involved.
--
--   Differences from the source:
--   - reading: N(V*_{j*} − V*) ≤ O(√N) → ∃ C, ∀ N ≥ 1: N(V*_{j*} − V*) ≤ C√N; reason: C may depend on the instance, not on N
--   - encoding: V*_{j*} with j* = argmin_{j ∈ [J]} V*_j → sInf of the finite nonempty set {V*(δ_j) : j ∈ [J]}; reason: the minimum of a finite nonempty set; J ≥ 1 for N ≥ 1
--   - reading: V* := V(δ*, S*) for the clairvoyant optimal (δ*, S*) policy of Theorem 1, with S* ≤ β; (9) and Table 3 write V* = min_{δ,S} V(δ, S) → V* = sInf of V(δ, S) = E[G]/E[L] over 0 ≤ δ ≤ S ≤ β; reason: Theorem 1 (Zheng 1991) is cited, not formalized; the paper's analysis (Theorem 2, Proposition 1) works on 0 ≤ δ ≤ S ≤ β. If never ordering (s < 0) were the clairvoyant optimum, V(δ*, S*) would be undefined, so the paper's V* is read as this minimum; the set is nonempty and bounded (|V| ≤ γ)
--   - reading: c and h are per-unit ordering and holding costs, sign not stated (p.7) → c ≥ 0 and h > 0; reason: costs are nonnegative; (19) divides by h, and for c < 0 the bound γ of (10) can be negative, so Lemma 1 would fail
--   - reading: i.i.d. continuous demands whose pdf satisfies f(d) ≤ ρ for d ≥ 0 (Assumption 1) → D t measurable, iIndepFun, IdentDistrib to D 0, and the law of D 0 is ≤ ρ·Lebesgue on [0, ∞); reason: demands are nonnegative quantities (Lemma 2 and the proof of Lemma 3: "D is positive"); the measure inequality is exactly a Lebesgue density bounded by ρ and supported on [0, ∞)
--   - encoding: periods t = 1, 2, … → 0-based: D t is the demand of period t + 1; reason: Lean indexing; no instance changes
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Proposition 1, eq. (26), p.21; j* from Bridging Policy III, p.20

import Mathlib
import Definitions.Def_DeltaSLearning_IsDemandProcess
import Definitions.Def_DeltaSLearning_optAvgCostGap
import Definitions.Def_DeltaSLearning_optAvgCost
import Definitions.Def_DeltaSLearning_grid

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Proposition 1** (discretization loss bound). With `J = ⌊√N⌋` and the grid
`δ_j = jβ/J`, the best grid value `V*_{j*} = min_{j ∈ [J]} V*(δ_j)` satisfies
`N (V*_{j*} - V*) ≤ O(√N)`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Proposition 1 and eq. (26), p.21; `j*` from Bridging Policy III, p.20.

**Formalization Note** The `O(·)` is read as `∃ C ∀ N ≥ 1`. The minimum over `[J]` is the
`sInf` of a finite nonempty set (`J ≥ 1` for `N ≥ 1`). No algorithm is involved. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (cp : Params) (hD : IsDemandProcess P D cp.ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) * (sInf ((fun j => optAvgCostGap P D cp (grid cp.β ⌊Real.sqrt N⌋₊ j)) ''
          Set.Icc 1 ⌊Real.sqrt N⌋₊) - optAvgCost P D cp) ≤ C * Real.sqrt N := by sorry

end DeltaSLearning
