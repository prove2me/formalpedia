-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_weighted_sphere_reeb_exists_unique
-- name    : BirkhoffGlobalSection.weighted_sphere_reeb_exists_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:12:54.97926+00:00
-- url     : https://prove2.me/theorems/262128db-5628-443b-9169-5aa8cd5974b9
-- title:
--   Weighted sphere reeb exists unique
-- statement:
--   At a unit-sphere point with a positive differentiable weight, there is exactly one sphere-tangent vector with weighted contact value one and zero exterior pairing against every sphere-tangent vector.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.weighted_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_weighted_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_weighted_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.weighted_sphere_reeb_exists_unique :
∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u),
    ∃! R : Phase,
      u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 ∧
      f u * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0) := by sorry
