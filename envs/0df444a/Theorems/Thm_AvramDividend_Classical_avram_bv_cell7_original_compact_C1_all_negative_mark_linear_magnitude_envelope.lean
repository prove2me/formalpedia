-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compact_C1_all_negative_mark_linear_magnitude_envelope
-- name    : AvramDividend.Classical.avram_bv_cell7_original_compact_C1_all_negative_mark_linear_magnitude_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:29:12.078205+00:00
-- url     : https://prove2.me/theorems/c1f61b51-17bb-48cc-9240-0dfa826a0013
-- title:
--   Uniform small and large original C1 negative-mark absolute value envelope
-- statement:
--   On the original positive compact state band [a,b], a locally C1 value candidate with Lipschitz constant L on [a/2,b] and global upper-reserve value bound R has its absolute negative-mark nonlinear jump difference bounded by (L+4R/a)|z| for every z<0. Small marks remain in the C1 band, and large marks are controlled by the global two-value bound. These constants come directly from the already Proved original BV localisation theorem; this deterministic lemma is a separately provable building block for the genuine original Lévy NX jump integrability certificate.

import Mathlib

open Set
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_compact_C1_all_negative_mark_linear_magnitude_envelope
    (w : ℝ → ℝ) (a b L R : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (y z : ℝ) (hy : y ∈ Icc a b) (hz : z < 0) :
    |w (y + z) - w y| ≤ (L + 4 * R / a) * (-z) := by sorry
