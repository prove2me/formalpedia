-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_weighted_sphere_reeb_formula_smooth
-- name    : BirkhoffGlobalSection.weighted_sphere_reeb_formula_smooth
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:13:04.471461+00:00
-- url     : https://prove2.me/theorems/db8e5e49-d0df-4fe8-9234-1bf93e8d7faf
-- title:
--   Weighted sphere reeb formula smooth
-- statement:
--   The explicit weighted-sphere Reeb formula is smooth wherever its weight is smooth and positive.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 3 of the Proved theorem BirkhoffGlobalSection.weighted_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_weighted_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_weighted_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.weighted_sphere_reeb_formula_smooth :
∀ (f : Phase → ℝ) (u : Phase)
    (hf : ContDiffAt ℝ ∞ f u) (hpos : 0 < f u),
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let g : Phase → Phase := fun x i => fderiv ℝ f x (coordinateVector i)
    let R : Phase → Phase := fun x => ((f x) ^ 2)⁻¹ •
      ((2 * f x + fderiv ℝ f x x) • J x - J (g x) -
        (fderiv ℝ f x (J x)) • x)
    ContDiffAt ℝ ∞ R u := by sorry
