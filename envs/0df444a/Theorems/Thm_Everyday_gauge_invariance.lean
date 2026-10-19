-- Prove2me | Theorems.Thm_Everyday_gauge_invariance
-- name    : Everyday.gauge_invariance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T00:15:36.50233+00:00
-- url     : https://prove2.me/theorems/ec09a6e4-3ef8-4ed8-8afe-2f3b3bcbda7e
-- title:
--   Other forces: the gauge functional is unchanged by a gauge shift of the gauge field
-- statement:
--   The image's "other forces" label is the Yang–Mills kinetic term -(1/4) F^a_μν F^{aμν} — the sector of electromagnetism and the nuclear forces, and the sector whose defining structural feature is gauge redundancy: the field strength, and therefore the action, is unchanged under the gauge transformation A_μ ↦ A_μ + ∂_μ χ. The item is the gauge redundancy in the discrete arena, whose gauge field is an abelian field on the oriented edges of the complete graph and whose field strength is the curl around triangles: when the edge field A is shifted along every edge by the discrete gradient of an arbitrary function χ — A x y ↦ A x y + (χ y - χ x), the discrete analogue of the gauge transformation — the curl around every triangle is unchanged, the gradient's curl cancelling around the closed triangle exactly as the mixed partials of ∂_μ χ commute in the continuum. Therefore the gauge sector's functional, the weighted sum of squared curls, is unchanged by the shift.
--
--   **Formalization Note** The abelian gauge field on the complete graph's oriented edges is the arena's stand-in for the Yang–Mills sector; the abelian case already carries the sector's structural fact. The triangle weights w are arbitrary, and no hypothesis is placed on χ — the gauge function is arbitrary, exactly as in the continuum. The proof: the curl of the shifted field around the triangle (x, y, z) is (A x y + χ y - χ x) - (A x z + χ z - χ x) + (A y z + χ z - χ y), in which the χ terms cancel around the closed triangle, leaving A x y - A x z + A y z pointwise; the functionals are then sums of the same summands.
-- source:
--   Sean Carroll, "The World of Everyday Experience, In One Equation", preposterousuniverse.com, 2013-01-04, retrieved 2026-10-18, the other-forces label -(1/4) F_μν^a F^{aμν}

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

namespace Everyday

/-- Other forces: the gauge redundancy. On the discrete spacetime, the
field strength of A is unchanged when A is shifted along every edge by
the discrete gradient of an arbitrary function χ — A x y ↦ A x y +
(χ y - χ x), the discrete analogue of A_μ ↦ A_μ + ∂_μ χ — and so the
gauge sector's functional is unchanged by the shift. -/
theorem gauge_invariance {X : Type} [Fintype X] (w : X → X → X → ℝ) (A : X → X → ℝ)
    (χ : X → ℝ) :
    gaugeAction w (fun x y => A x y + (χ y - χ x)) = gaugeAction w A := by sorry

end Everyday
