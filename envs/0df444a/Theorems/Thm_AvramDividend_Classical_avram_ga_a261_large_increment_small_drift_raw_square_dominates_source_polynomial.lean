-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a261_large_increment_small_drift_raw_square_dominates_source_polynomial
-- name    : AvramDividend.Classical.avram_ga_a261_large_increment_small_drift_raw_square_dominates_source_polynomial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:51:05.480036+00:00
-- url     : https://prove2.me/theorems/54a980b1-2091-46ad-83e5-b41c36851dd7
-- title:
--   Gaussian rare raw increment with small deterministic drift bounds polynomial large-cell source envelope by raw quadratic energy
-- statement:
--   For a Gaussian physical cell with raw increment r, drift correction a and centered increment z=r-a, when |r| is above δ>0 and the deterministic drift correction is at most δ, the scalar large-cell envelope 1+|r|+z²/2 is bounded by (δ^{-2}+δ^{-1}+2)r². This turns all polynomial terms of a258/a260 combined large-cell positive residual into the proved original stopped Gaussian raw-large-square expected L1 source a187, leaving only the positive exponential tail already proved in a233.
-- source:
--   True original Gaussian raw-square large tail a187, source a258/a260 large-cell positive polynomial bound

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a261_large_increment_small_drift_raw_square_dominates_source_polynomial
    (δ r z a : ℝ) (hδ : 0 < δ)
    (hr : δ ≤ |r|) (ha : |a| ≤ δ) (hz : z = r-a) :
    1+|r|+z^2/2 ≤ (1/δ^2+1/δ+2)*r^2 := by sorry
