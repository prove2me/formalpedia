-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_time_change_functional_coefficient_continuous
-- name    : BirkhoffGlobalSection.time_change_functional_coefficient_continuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:30.368701+00:00
-- url     : https://prove2.me/theorems/d68e4333-e29b-430e-b988-c336125f545a
-- title:
--   Time change functional coefficient continuous
-- statement:
--   Along a supplied continuous trajectory and variational matrix, the displayed inverse-clock functional coefficient is continuous when the scalar rate is smooth along the trajectory and never vanishes.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.model_contact_rate_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_model_contact_rate_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_model_contact_rate_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.time_change_functional_coefficient_continuous :
∀ (b : Phase → ℝ) (x : ℝ → Phase) (C : ℝ ≃o ℝ)
    (Z : ℝ → (Phase →L[ℝ] Phase))
    (hx : Continuous x) (hZ : Continuous Z)
    (hb : ∀ t, ContDiffAt ℝ ∞ b (x t)) (hne : ∀ t, b (x t) ≠ 0),
    Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t)))) := by sorry
