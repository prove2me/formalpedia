-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_moving_band_taylor_lagrange
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_moving_band_taylor_lagrange
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:26:27.531518+00:00
-- url     : https://prove2.me/theorems/342ee05e-4990-4b84-8912-62c6f8f7491e
-- title:
--   Moving-anchor exact Gaussian Taylor remainder inside the original strict C2 band
-- statement:
--   For arbitrary two distinct original-controlled reserve levels u,v lying in a single compact interval inside the exact 0<y<C source C2 interior, the first-order Taylor remainder from u to v is exactly half the second ordinary iterated derivative at an intermediate ξ times (v-u)^2. The full unordered interval between reserve levels remains inside the strict source interior. This moving-anchor formula is the exact deterministic ingredient for Gaussian Itô mesh error, with no global C2, cross-ruin continuity, Brownian representation or boundary occupation claim.
-- source:
--   Avram Palmowski Pistorius Proposition 4(i), exact pinned Mathlib Taylor mean-remainder-Lagrange iteratedDeriv and Set.uIcc_subset_Icc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_moving_band_taylor_lagrange
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b)
    (huv : u ≠ v) :
    ∃ ξ ∈ uIoo u v,
      w v - taylorWithinEval w 1 (uIcc u v) u v =
        iteratedDeriv 2 w ξ * (v - u) ^ 2 / 2 := by sorry
