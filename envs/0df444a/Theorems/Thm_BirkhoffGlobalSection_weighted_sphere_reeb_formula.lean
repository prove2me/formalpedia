-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_weighted_sphere_reeb_formula
-- name    : BirkhoffGlobalSection.weighted_sphere_reeb_formula
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:12:52.678978+00:00
-- url     : https://prove2.me/theorems/b4fd2657-d57d-4cfd-9fbb-5097b3c88772
-- title:
--   Weighted sphere reeb formula
-- statement:
--   A positive weight differentiable at a point of the unit three-sphere has the stated explicit Reeb vector, expressed using the weight differential and the standard complex rotation.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.weighted_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_weighted_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_weighted_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.weighted_sphere_reeb_formula :
∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u),
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let L := fderiv ℝ f u
    let g : Phase := fun i => L (coordinateVector i)
    let R : Phase := ((f u) ^ 2)⁻¹ •
      ((2 * f u + L u) • J u - J g - L (J u) • u)
    (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
    (f u * phaseRadialContact u R = 1) ∧
    (∀ w : Phase,
      u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
        fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0) := by sorry
