-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_NearOne_theorem_4a
-- name    : BlackwellDiscreteDP.NearOne.theorem_4a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:23:40.667985+00:00
-- url     : https://prove2.me/theorems/ee86d5a5-dfd5-4aa0-97da-ff0e87b3d765
-- title:
--   Theorem 4(a) — V_β(f) = x(f)/(1 − β) + y(f) + ε(β, f) with ε(β, f) → 0 as β → 1
-- statement:
--   In the finite decision model, take any decision rule $f\in F$ and let $Q^*(f)$ be the limit matrix of $Q(f)$. Then
--   $$V_\beta(f^{(\infty)})=\frac{x(f)}{1-\beta}+y(f)+\varepsilon(\beta,f),$$
--   where $x(f)$ is the unique solution of
--   $$(I-Q(f))x=0,\qquad Q^*(f)x=Q^*(f)r(f),$$
--   $y(f)$ is the unique solution of
--   $$(I-Q(f))y=r(f)-x(f),\qquad Q^*(f)y=0,$$
--   and $\varepsilon(\beta,f)\to0$ as $\beta\to1$.
--
--   The pole coefficient $x(f)$ is the average income of $f^{(\infty)}$ and the constant term $y(f)$ its bias; all comparisons of stationary policies near $\beta=1$ in Theorem 4 go through this expansion.
--
--   **Formalization Note** $x(f)$ and $y(f)$ are defined as $Q^*(f)r(f)$ and $H(f)r(f)$; the statement asserts that each is the one and only solution of its system, and that $V_\beta(f^{(\infty)})-x(f)/(1-\beta)-y(f)\to0$ as $\beta\to1$ from below.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 722, Theorem 4(a)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- **Theorem 4(a).** For any `f ∈ F`,
`V_β(f) = x(f)/(1 − β) + y(f) + ε(β, f)` where `x(f)` is the unique solution of
`(I − Q(f))x = 0, Q*(f)x = Q*(f)r(f)`, `y(f)` is the unique solution of
`(I − Q(f))y = r(f) − x(f), Q*(f)y = 0`, and `ε(β, f) → 0` as `β → 1`.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 722, Theorem 4(a).

**Formalization Note.** `x(f) := Q*(f)r(f)` and `y(f) := H(f)r(f)` are defined by the closed
forms of the paper's proof; the first two conjuncts say they are exactly the solutions of the two
systems (each system has the stated vector as its only solution). `ε(β, f)` is
`V_β(f^(∞)) − x(f)/(1 − β) − y(f)`, and the limit is along `𝓝[<] 1`. -/
theorem theorem_4a {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    (∀ z : St → ℝ, ((1 - M.Q f) *ᵥ z = 0 ∧ M.Qstar f *ᵥ z = M.Qstar f *ᵥ M.r f) ↔ z = M.x f) ∧
      (∀ z : St → ℝ, ((1 - M.Q f) *ᵥ z = M.r f - M.x f ∧ M.Qstar f *ᵥ z = 0) ↔ z = M.y f) ∧
      Tendsto (fun β : ℝ => M.V β (Policy.stationary f) - (1 - β)⁻¹ • M.x f - M.y f)
        (𝓝[<] 1) (𝓝 0) := by sorry

end BlackwellDiscreteDP.NearOne
