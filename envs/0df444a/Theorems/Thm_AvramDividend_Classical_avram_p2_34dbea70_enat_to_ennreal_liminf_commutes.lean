-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_enat_to_ennreal_liminf_commutes
-- name    : AvramDividend.Classical.avram_p2_34dbea70_enat_to_ennreal_liminf_commutes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:27:26.8673+00:00
-- url     : https://prove2.me/theorems/34dc1801-1022-48fe-8d61-e2250d464442
-- title:
--   ENat-to-ENNReal conversion commutes with sequential filter liminf
-- statement:
--   For any sequence u : Nat → ENat, converting its filter-atTop liminf to ENNReal equals the ENNReal liminf of the pointwise converted sequence, including infinite values. This follows from the pinned complete-lattice iSup/iInf formula for liminf and the pinned ENat.toENNReal_iSup/iInf theorems. It is the exact non-finite-activity bridge between the accepted original pathwise negative-jump encard liminf and the ENNReal Fatou expectation bound.

import Mathlib

open Filter
open scoped ENat ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_enat_to_ennreal_liminf_commutes
    (u : ℕ → ℕ∞) :
    ENat.toENNReal (Filter.liminf u atTop) =
      Filter.liminf (fun n : ℕ => ENat.toENNReal (u n)) atTop := by sorry
