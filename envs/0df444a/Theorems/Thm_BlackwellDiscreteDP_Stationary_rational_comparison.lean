-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_Stationary_rational_comparison
-- name    : BlackwellDiscreteDP.Stationary.rational_comparison
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:02:08.357038+00:00
-- url     : https://prove2.me/theorems/29a35803-df78-4d99-ba00-2c3482ef9f2a
-- title:
--   Proof of Theorem 5 (pp. 725–726) — V_β(f*) ≧ V_β(g) on β's accumulating at 1 implies it for all β near 1
-- statement:
--   Let $f^*$ and $g$ be decision rules. Suppose that
--
--   $$V_\beta(f^{*(\infty)})\ge V_\beta(g^{(\infty)})$$
--
--   (coordinatewise) for a set of $\beta<1$ having $1$ as a limit point, i.e. for every $\beta_0<1$ there is such a $\beta\in(\beta_0,1)$. Then there is $\beta_0<1$ such that the same inequality holds for every $\beta\in(\beta_0,1)$.
--
--   This is the step where the rationality of the returns in $\beta$ is used; it upgrades "infinitely often near $1$" to "for all $\beta$ near $1$".
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, pp. 725–726, §4, proof of Theorem 5

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- §4, proof of Theorem 5, pp. 725–726 (unnumbered; Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"Then, for every g, V_β(f*) ≧ V_β(g) for a set of β's having 1 as a limit point. Since all
coordinates of V_β(f*) and V_β(g) are rational functions of β, V_β(f*) ≧ V_β(g) for all β near 1."

For decision rules `f*`, `g`: if `V_β(f*^(∞)) ≧ V_β(g^(∞))` (the whole vector) for a set of
`β < 1` having `1` as a limit point, then it holds for all `β` in some interval `(β₀, 1)`. -/
theorem rational_comparison {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (fstar g : St → Act)
    (h : ∀ β₀ : ℝ, β₀ < 1 → ∃ β : ℝ, β₀ < β ∧ β < 1 ∧
      M.V β (stationary g) ≤ M.V β (stationary fstar)) :
    ∃ β₀ : ℝ, β₀ < 1 ∧ ∀ β : ℝ, β₀ < β → β < 1 →
      M.V β (stationary g) ≤ M.V β (stationary fstar) := by sorry

end BlackwellDiscreteDP.Stationary
