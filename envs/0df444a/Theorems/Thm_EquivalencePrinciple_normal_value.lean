-- Prove2me | Theorems.Thm_EquivalencePrinciple_normal_value
-- name    : EquivalencePrinciple.normal_value
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T00:56:23.291798+00:00
-- url     : https://prove2.me/theorems/ad2e96bf-d279-5df5-81b6-0247bb07b0f0
-- title:
--   Zeroth-order local flatness (Minkowski value by linear change)
-- statement:
--   **Zeroth-order local flatness — the entry rung.**
--
--   Let `S` be a metric spacetime (a twice continuously differentiable field of symmetric nondegenerate bilinear forms of Lorentz signature on $\mathbb{R}^4$, with carried witnesses) and `p` any point.
--
--   **Conclusion:** there is an invertible $4 \times 4$ real matrix $B$ with
--
--   $$B^T\, (g_{ij}(p))_{i,j}\, B \;=\; \mathrm{diag}(-1, 1, 1, 1).$$
--
--   In words: by a linear change of coordinates, the metric value at any single point can be made exactly Minkowski. Mathematically this restates the carried Lorentz-signature witness `hB` of the spacetime structure — it is the trivial half of the local equivalence of a gravitational field and an accelerated frame; the content of the equivalence principle begins where this rung ends, with the removal of the first-order corrections (the goal theorem).
-- source:
--   Wikipedia, Equivalence principle, https://en.wikipedia.org/wiki/Equivalence_principle (source of the quoted statements, reproduced verbatim in the definition file) (Einstein equivalence principle; 'metric theories'); C. W. Misner, K. S. Thorne, J. A. Wheeler, Gravitation (1973), Riemann normal coordinates

import Mathlib
import Definitions.Def_EquivalencePrinciple

namespace EquivalencePrinciple

open Matrix

/-- Milestone (entry rung): zeroth-order local flatness.  At every point of a
metric spacetime the metric is congruent to the Minkowski diagonal by an
invertible linear change of coordinates — the carried Lorentz-signature
witness.  This is the trivial half of the local equivalence of a gravitational
field and an accelerated frame: the metric value itself can always be made
Minkowski; the content of the equivalence principle is that the first-order
corrections can be removed too (see `local_minkowski_first_order`). -/
theorem normal_value (S : Spacetime) (p : Sp) :
    ∃ B : Matrix (Fin 4) (Fin 4) ℝ, IsUnit B.det ∧
      Bᵀ * (Matrix.of fun i j => S.g p i j) * B = Matrix.diagonal minkowskiDiag := by
  sorry

end EquivalencePrinciple
