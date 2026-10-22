-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_weighted_contact_curve_derivative
-- name    : BirkhoffGlobalSection.weighted_contact_curve_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:43:43.71543+00:00
-- url     : https://prove2.me/theorems/a2caa48e-9c06-4944-aefa-5e3476df8d54
-- title:
--   Weighted contact curve derivative
-- statement:
--   Along differentiable base and vector curves, a differentiable weighted radial contact pairing obeys the displayed scalar and bilinear product-rule derivative formula.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.contact_variation_preservation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_variation_preservation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.weighted_contact_curve_derivative :
∀ (f : Phase → ℝ) (q v : ℝ → Phase)
    (t : ℝ) (a b : Phase) (hf : DifferentiableAt ℝ f (q t))
    (hq : HasDerivAt q a t) (hv : HasDerivAt v b t),
    HasDerivAt (fun s => f (q s) * phaseRadialContact (q s) (v s))
      (fderiv ℝ f (q t) a * phaseRadialContact (q t) (v t) +
        f (q t) * (phaseRadialContact a (v t) + phaseRadialContact (q t) b)) t := by sorry
