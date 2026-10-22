-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_contact_curve_derivative
-- name    : BirkhoffGlobalSection.radial_contact_curve_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:43:51.143663+00:00
-- url     : https://prove2.me/theorems/03c2655d-a0dc-43f3-9c5c-7bda96db233e
-- title:
--   Radial contact curve derivative
-- statement:
--   Along two differentiable phase curves, the radial contact pairing obeys the bilinear product-rule derivative formula.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.contact_variation_preservation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_variation_preservation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.radial_contact_curve_derivative :
∀ (q v : ℝ → Phase) (t : ℝ) (a b : Phase)
    (hq : HasDerivAt q a t) (hv : HasDerivAt v b t),
    HasDerivAt (fun s => phaseRadialContact (q s) (v s))
      (phaseRadialContact a (v t) + phaseRadialContact (q t) b) t := by sorry
