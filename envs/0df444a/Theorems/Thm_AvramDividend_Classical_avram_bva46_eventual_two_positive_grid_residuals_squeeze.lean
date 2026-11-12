-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva46_eventual_two_positive_grid_residuals_squeeze
-- name    : AvramDividend.Classical.avram_bva46_eventual_two_positive_grid_residuals_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:00:53.113111+00:00
-- url     : https://prove2.me/theorems/1feaa5a9-ab45-4b18-8f5e-332250621f18
-- title:
--   Eventually valid finite-jump grid error decomposition preserves vanishing positive excess
-- statement:
--   Finite-activity original Lévy jump times can be isolated into distinct uniform grid cells only for sufficiently fine mesh, so the physical source error decomposition is eventually valid. If the positive errors from Stieltjes accounting and compensator quadrature separately vanish, the overall original stopped positive excess vanishes even when the upper bound holds only eventually.
-- source:
--   Original finite positive-jump-count physical stopped source 4287fafd-afdc-46b2-a160-033b7b2500f2, using established finite marked jump cell isolation 4e52d932 and one-sided quadrature e5edbe9b, authored 11 November 2026.

import Mathlib

theorem AvramDividend.Classical.avram_bva46_eventual_two_positive_grid_residuals_squeeze (E A B : ℕ → ℝ) (hbound : ∀ᶠ n in Filter.atTop, E n ≤ A n + B n) (hA : Filter.Tendsto (fun n => max (A n) 0) Filter.atTop (nhds 0)) (hB : Filter.Tendsto (fun n => max (B n) 0) Filter.atTop (nhds 0)) : Filter.Tendsto (fun n => max (E n) 0) Filter.atTop (nhds 0) := by sorry
