-- Prove2me | Theorems.Thm_DiffCtrlRobust_theorem_3_1
-- name    : DiffCtrlRobust.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:37.991717+00:00
-- url     : https://prove2.me/theorems/7cae2dad-42d2-4acc-9b55-003a6c49c532
-- title:
--   Theorem 3.1 — $V_\alpha$ is the unique $\mathcal C^2\cap\mathcal C_b$ solution of the HJB equation; optimal controls are its minimizing selectors
-- statement:
--   Let $\alpha>0$ and suppose (A1)–(A4) hold. Then the optimal discounted cost $V_\alpha$ of (2.3) lies in $\mathcal C^2(\mathbb R^d)\cap\mathcal C_b(\mathbb R^d)$ and solves
--
--   $$
--   \min_{\zeta\in\mathbb U}\big[\mathcal L_\zeta V_\alpha(x)+c(x,\zeta)\big]=\alpha V_\alpha(x)\qquad\text{for all }x\in\mathbb R^d,
--   $$
--
--   and every solution in that class equals $V_\alpha$. Moreover, $v\in\mathfrak U_{\mathsf{sm}}$ is $\alpha$-discounted optimal if and only if it is a measurable minimizing selector, (3.2).
--
--   This is the characterization of the discounted problem that the continuity and robustness results use.
--
--   Differences from the source:
--
--   - encoding: complete probability space (Ω, 𝔉, ℙ) → any probability space, with the null sets joined to the filtrations explicitly; reason: the filtrations are the same up to null sets and no argument needs more; every complete space is included
--   - encoding: V-valued process U, 𝔘 implicit → jointly measurable U, admissible pairs (U, X) with X adapted to 𝔉; reason: makes 'V valued process' and 'strong solution' precise; the same controls
--   - encoding: optimal: cost equals the value for all x → also requires a solution under v from every x; reason: the clause only excludes vacuous optimality; it holds under (A1)–(A3)
--   - encoding: sup over ζ in (A2) → a bound for every ζ; reason: equivalent for nonempty U
--   - encoding: U a compact metric space, min over U → U also nonempty; reason: a minimum over U presupposes it
--   - encoding: min over U in the HJB equation → ⨅ over U; reason: the expression is continuous on compact U, so the infimum is attained
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, Theorem 3.1, p.10, citing [9, Theorem 3.5.6]

import Definitions.Def_DiffCtrlRobust_A123
import Definitions.Def_DiffCtrlRobust_CostRegular
import Definitions.Def_DiffCtrlRobust_IsDiscOptimal
import Definitions.Def_DiffCtrlRobust_IsHJBSolution
import Definitions.Def_DiffCtrlRobust_IsMinimizingSelector
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- Theorem 3.1 (arXiv:2205.05894v2, p.10): under (A1)–(A4), the optimal discounted cost `V_α` of
(2.3) is the unique solution in `C²(ℝ^d) ∩ C_b(ℝ^d)` of the HJB equation (3.1), and `v ∈ 𝔘sm` is
`α`-discounted optimal if and only if it is a measurable minimizing selector, (3.2). -/
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {U : Type*} [MetricSpace U] [CompactSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {α : ℝ} (hα : 0 < α) {C : ℝ → ℝ} {C₀ M : ℝ} {b : SDEState d → U → SDEState d}
    {σ : SDEState d → SDEDiffusion d} {c : SDEState d → U → ℝ}
    (hA : A123 C C₀ b σ) (hc : CostRegular M c) (hc0 : ∀ x ζ, 0 ≤ c x ζ) :
    IsHJBSolution α b σ c (value P W α b σ c) ∧
    (∀ V, IsHJBSolution α b σ c V → V = value P W α b σ c) ∧
    (∀ v : Usm d U, IsDiscOptimal P W α b σ c v ↔
      IsMinimizingSelector b c (value P W α b σ c) v) := by sorry

end DiffCtrlRobust
