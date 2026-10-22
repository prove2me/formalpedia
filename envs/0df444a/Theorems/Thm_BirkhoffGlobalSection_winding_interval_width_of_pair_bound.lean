-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_winding_interval_width_of_pair_bound
-- name    : BirkhoffGlobalSection.winding_interval_width_of_pair_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:51:41.31726+00:00
-- url     : https://prove2.me/theorems/e4af1ea1-2b52-42be-bc94-bdb3e4292251
-- title:
--   Winding interval width of pair bound
-- statement:
--   If an attained winding image is [a,b] and every two values differ by less than one half, its width b−a is strictly less than one half.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 5 of the Proved theorem BirkhoffGlobalSection.contact_winding_width_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_winding_width_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_width_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.winding_interval_width_of_pair_bound :
∀ (d : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (himage : d '' Icc 0 (2 * Real.pi) = Icc a b)
    (hbound : ∀ s r, |d r - d s| < 1 / 2),
    b - a < 1 / 2 := by sorry
