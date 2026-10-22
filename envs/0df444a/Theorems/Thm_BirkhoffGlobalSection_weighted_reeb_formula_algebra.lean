-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_weighted_reeb_formula_algebra
-- name    : BirkhoffGlobalSection.weighted_reeb_formula_algebra
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:14.572987+00:00
-- url     : https://prove2.me/theorems/d3bb0e8e-29e3-4a05-a1ca-208531627b71
-- title:
--   Weighted reeb formula algebra
-- statement:
--   For a unit-sphere point, positive scalar weight and supplied continuous linear coefficient L, the displayed explicit quaternionic formula satisfies tangency, contact normalization and the algebraic Reeb pairing identities.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_weighted_reeb_bundle.lean:22. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_BirkhoffGlobalSection_weighted_sphere_contact_geometry
import Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_contact_weight
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false




set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.weighted_reeb_formula_algebra (u : Phase) (hu : u ∈ unitThreeSphere)
    (a : ℝ) (ha : 0 < a) (L : Phase →L[ℝ] ℝ) :
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let g : Phase := fun i => L (coordinateVector i)
    let R : Phase := (a ^ 2)⁻¹ • ((2 * a + L u) • J u - J g - L (J u) • u)
    (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
      a * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        L R * phaseRadialContact u w - L w * phaseRadialContact u R -
          a * phaseSymplecticForm R w = 0) := by sorry
