-- Prove2me | Theorems.Thm_DeltaSLearning_theorem_2_c
-- name    : DeltaSLearning.theorem_2_c
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:09:43.431652+00:00
-- url     : https://prove2.me/theorems/ba168e80-029b-494a-a4d9-b8efd4c9709b
-- title:
--   Theorem 2(c) — $V^*(\delta)$ is Lipschitz in $\delta$
-- statement:
--   Assume Assumption 1 and the cost parameters of §2. The optimized objective $V^*(\delta)=\min_{S\in[\delta,\beta]}V(\delta,S)$ is Lipschitz on $[0,\beta]$: there is $M'$ with
--   $$|V^*(\delta_1)-V^*(\delta_2)|\le M'|\delta_1-\delta_2|\qquad(\delta_1,\delta_2\in[0,\beta]).$$
--
--   This bounds the loss of restricting the gap to the grid $\{j\beta/J\}$ (Proposition 1).
--
--   Differences from the source:
--   - reading: c and h are per-unit ordering and holding costs, sign not stated (p.7) → c ≥ 0 and h > 0; reason: costs are nonnegative; (19) divides by h, and for c < 0 the bound γ of (10) can be negative, so Lemma 1 would fail
--   - reading: i.i.d. continuous demands whose pdf satisfies f(d) ≤ ρ for d ≥ 0 (Assumption 1) → D t measurable, iIndepFun, IdentDistrib to D 0, and the law of D 0 is ≤ ρ·Lebesgue on [0, ∞); reason: demands are nonnegative quantities (Lemma 2 and the proof of Lemma 3: "D is positive"); the measure inequality is exactly a Lebesgue density bounded by ρ and supported on [0, ∞)
--   - encoding: periods t = 1, 2, … → 0-based: D t is the demand of period t + 1; reason: Lean indexing; no instance changes
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 2(c), eq. (12), p.12

import Mathlib
import Definitions.Def_DeltaSLearning_IsDemandProcess
import Definitions.Def_DeltaSLearning_optAvgCostGap

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Theorem 2(c)**. The objective with the target optimized,
`V*(δ) := min_{S ∈ [δ, β]} V(δ, S)` of (12), is Lipschitz in `δ ∈ [0, β]`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 2(c) and eq. (12), p.12. -/
theorem theorem_2_c {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (cp : Params) (hD : IsDemandProcess P D cp.ρ) :
    ∃ M : NNReal, LipschitzOnWith M (fun δ => optAvgCostGap P D cp δ) (Set.Icc 0 cp.β) := by sorry

end DeltaSLearning
