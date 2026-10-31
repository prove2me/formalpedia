-- Prove2me | Theorems.Thm_DiffCtrlRobust_theorem_3_2
-- name    : DiffCtrlRobust.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:15.236739+00:00
-- url     : https://prove2.me/theorems/5fd8d95d-3118-40c4-b868-b1f5efc4bcd5
-- title:
--   Theorem 3.2 — the HJB characterization for one approximating model, with a real-valued cost
-- statement:
--   Let $\alpha>0$ and fix $n$. Suppose $(b_n,\sigma_n)$ satisfies (A1)–(A3), and $c_n$ is bounded by $M$, jointly continuous, and locally Lipschitz in $x$ uniformly in $\zeta$. Then there is a unique $V^n_\alpha\in\mathcal C^2(\mathbb R^d)\cap\mathcal C_b(\mathbb R^d)$ with
--
--   $$
--   \min_{\zeta\in\mathbb U}\big[\mathcal L^n_\zeta V^n_\alpha(x)+c_n(x,\zeta)\big]=\alpha V^n_\alpha(x)\qquad\text{for all }x\in\mathbb R^d.
--   $$
--
--   Moreover:
--
--   1. $V^n_\alpha$ is the optimal discounted cost: $V^n_\alpha(x)=\inf_{U\in\mathfrak U}\mathbb E^U_x\left[\int_0^\infty e^{-\alpha s}c_n(X^n_s,U_s)\,\mathrm ds\right]$ for all $x$;
--   2. $v\in\mathfrak U_{\mathsf{sm}}$ is $\alpha$-discounted optimal for the model if and only if it is a measurable minimizing selector of this equation, (3.4).
--
--   The Lean statement treats one model, so the constants of (A1)–(A3) are those of that model and the assumption is (A5)(iii) for a single $n$.
--
--   Differences from the source:
--
--   - encoding: complete probability space (Ω, 𝔉, ℙ) → any probability space, with the null sets joined to the filtrations explicitly; reason: the filtrations are the same up to null sets and no argument needs more; every complete space is included
--   - encoding: V-valued process U, 𝔘 implicit → jointly measurable U, admissible pairs (U, X) with X adapted to 𝔉; reason: makes 'V valued process' and 'strong solution' precise; the same controls
--   - encoding: optimal: cost equals the value for all x → also requires a solution under v from every x; reason: the clause only excludes vacuous optimality; it holds under (A1)–(A3)
--   - encoding: sup over ζ in (A2) → a bound for every ζ; reason: equivalent for nonempty U
--   - encoding: U a compact metric space, min over U → U also nonempty; reason: a minimum over U presupposes it
--   - encoding: min over U in the HJB equation → ⨅ over U; reason: the expression is continuous on compact U, so the infimum is attained
--   - reading: cₙ : ℝᵈ × U → ℝᵈ (p.7) → cₙ real valued with |cₙ| ≤ M, sign not assumed; reason: the printed codomain is a typo: cₙ is a scalar cost compared with c and bounded by M; not assuming cₙ ≥ 0 is the stronger reading
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, Theorem 3.2, p.11, citing [9, Theorem 3.5.6]

import Definitions.Def_DiffCtrlRobust_A123
import Definitions.Def_DiffCtrlRobust_CostRegular
import Definitions.Def_DiffCtrlRobust_IsDiscOptimal
import Definitions.Def_DiffCtrlRobust_IsHJBSolution
import Definitions.Def_DiffCtrlRobust_IsMinimizingSelector
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- Theorem 3.2 (arXiv:2205.05894v2, p.11), for one approximating model: under (A5)(iii) there is a
unique `V ∈ C²(ℝ^d) ∩ C_b(ℝ^d)` solving (3.3); (i) `V` is the optimal discounted cost; (ii) `v ∈ 𝔘sm`
is `α`-discounted optimal if and only if it is a measurable minimizing selector of (3.3), (3.4).

**Formalization Note.** The statement is for a single model `(b, σ, c)`, which is `(bₙ, σₙ, cₙ)` for
a fixed `n`, so its constants are its own. The cost is real valued and need not be nonnegative. -/
theorem theorem_3_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {U : Type*} [MetricSpace U] [CompactSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {α : ℝ} (hα : 0 < α) {C : ℝ → ℝ} {C₀ M : ℝ} {b : SDEState d → U → SDEState d}
    {σ : SDEState d → SDEDiffusion d} {c : SDEState d → U → ℝ}
    (hA : A123 C C₀ b σ) (hc : CostRegular M c) :
    ∃ V : SDEState d → ℝ, IsHJBSolution α b σ c V ∧
      (∀ V', IsHJBSolution α b σ c V' → V' = V) ∧
      (∀ x, V x = value P W α b σ c x) ∧
      (∀ v : Usm d U, IsDiscOptimal P W α b σ c v ↔ IsMinimizingSelector b c V v) := by sorry

end DiffCtrlRobust
