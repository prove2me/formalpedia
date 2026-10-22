-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_chart_variation_derivative
-- name    : BirkhoffGlobalSection.chart_variation_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:32.07398+00:00
-- url     : https://prove2.me/theorems/e83b028c-d62c-4599-b5a5-ee26c8400424
-- title:
--   Chart variation derivative
-- statement:
--   Along differentiable base and variation curves, differentiating a smooth chart's derivative applied to the variation gives the Hessian term plus the pushed variation derivative.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.chart_variation_derivative :
∀ (f : Phase → Phase) (q v : ℝ → Phase)
    (t : ℝ) (a b : Phase) (hf : ContDiffAt ℝ ∞ f (q t))
    (hq : HasDerivAt q a t) (hv : HasDerivAt v b t),
    HasDerivAt (fun s => fderiv ℝ f (q s) (v s))
      (fderiv ℝ (fderiv ℝ f) (q t) a (v t) + fderiv ℝ f (q t) b) t := by sorry
