-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_enat_mesh_liminf_casts_to_ennreal
-- name    : AvramDividend.Classical.avram_p2_enat_mesh_liminf_casts_to_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:14:37.407625+00:00
-- url     : https://prove2.me/theorems/0d6d01e5-1265-426e-b64d-6d897c81e3f8
-- title:
--   Mesh jump-count ENat liminf is preserved under ENNReal cast
-- statement:
--   For any sequence of extended natural-number uniform-mesh counts, the canonical continuous monotone embedding ENat.toENNReal preserves its atTop filter liminf. This genuinely bridges the original sample-path jump-cell bound, expressed in Set.encard and ℕ∞, into the ENNReal Fatou integral required for expected intrinsic jump counts. No Lévy-rate or compensator hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_enat_mesh_liminf_casts_to_ennreal (a : ℕ → ℕ∞) :
    ((Filter.liminf a Filter.atTop : ℕ∞) : ℝ≥0∞) =
      Filter.liminf (fun n => (a n : ℝ≥0∞)) Filter.atTop := by sorry
