-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_clipped_mesh_width
-- name    : AvramDividend.Classical.avram_jump6_B_canonical_clipped_mesh_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:30:46.571435+00:00
-- url     : https://prove2.me/theorems/a43bd9bd-2329-4c90-a21b-2ff66858cd20
-- title:
--   All original canonical stopped grid cells have width at most the refining mesh step
-- statement:
--   For every path and every original canonical physical mesh, clipping successive nonnegative-time grid points at the random stopped clock does not increase a grid-cell width. The upper endpoint is bounded by the preceding clipped endpoint plus 1/(j+1), uniformly in the path, index and resolution. Pure NNReal order arithmetic, independent of jump activity or Gaussian noise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open scoped NNReal

theorem AvramDividend.Classical.avram_jump6_B_canonical_clipped_mesh_width
    (j i : ℕ) (t : ℝ≥0) :
    min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t ≤
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t +
        (1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by sorry
