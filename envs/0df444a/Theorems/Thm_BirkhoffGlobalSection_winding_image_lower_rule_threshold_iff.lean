-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_winding_image_lower_rule_threshold_iff
-- name    : BirkhoffGlobalSection.winding_image_lower_rule_threshold_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:51:12.563991+00:00
-- url     : https://prove2.me/theorems/d51d636c-2c29-4132-ac6c-73995f1fc40a
-- title:
--   Winding image lower rule threshold iff
-- statement:
--   For a winding image equal to a closed interval of width below one, its ceiling sum minus one is at least 2k+1 exactly when every directional value exceeds k.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 10 of the Proved theorem BirkhoffGlobalSection.contact_winding_interval_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_winding_interval_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_interval_bundle

open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology

set_option maxHeartbeats 800000
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.winding_image_lower_rule_threshold_iff :
∀ (d : ℝ → ℝ) (a b : ℝ) (k : ℤ)
    (hab : a ≤ b) (hwidth : b - a < 1)
    (himage : d '' Icc 0 (2 * Real.pi) = Icc a b),
    2 * k + 1 ≤ Int.ceil a + Int.ceil b - 1 ↔
      ∀ s ∈ Icc 0 (2 * Real.pi), (k : ℝ) < d s := by sorry
