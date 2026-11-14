-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a113_original_gaussian_crossing_bounded_HJB_compensator_algebra
-- name    : AvramDividend.Classical.avram_ga_a113_original_gaussian_crossing_bounded_HJB_compensator_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:41:43.390854+00:00
-- url     : https://prove2.me/theorems/766a072e-2fc8-4a9b-a105-5ed01efb3b2c
-- title:
--   Original Gaussian crossing full-grid HJB compensator is bounded by two times coefficient envelope times source displacement, square and variance clock
-- statement:
--   For an actual Gaussian crossing cell, write its source HJB compensation as a first derivative coefficient times the full physical Gaussian source increment, a Hessian coefficient times increment-square minus quadratic-variance clock, and a generator coefficient times the physical clock. If each coefficient has absolute size at most a compact-localisation constant, the full absolute compensation is bounded by twice that constant times absolute source displacement, square and clock. This supplies the rigorous coefficient hypothesis for the vanishing-compensator lemma.
-- source:
--   Source-exact Gaussian physical stopping-cell compensated generator residual in the original Avram positive-domain Gaussian proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a113_original_gaussian_crossing_bounded_HJB_compensator_algebra
    (A B C z v K : ℝ) (hK : 0 ≤ K) (hv : 0 ≤ v)
    (hA : |A| ≤ K) (hB : |B| ≤ K) (hC : |C| ≤ K) :
    |A * z + B * (z^2 - v) + v * C| ≤
      (2 * K) * (|z| + z^2 + v) := by sorry
