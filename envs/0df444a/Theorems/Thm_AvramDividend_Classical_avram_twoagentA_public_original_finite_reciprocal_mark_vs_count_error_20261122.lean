-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_finite_reciprocal_mark_vs_count_error_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_finite_reciprocal_mark_vs_count_error_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:16:01.314804+00:00
-- url     : https://prove2.me/theorems/35c211cb-e93d-4729-8bcf-d2aee1c441d1
-- title:
--   Original true finite-band signed mark compensated count error bridge 1
-- statement:
--   Republish exact accepted physically marked signed-jump original-X finite reciprocal negative-band vs compensation and count-proxy error proof after replacing all private worker dependencies with equivalent Proved public original-X proof declarations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_physical_finite_band_signed_integral_partition_20261122
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_physical_signed_mark_constant_shift_integral_20261122
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_time_mark_negative_bin_integral_error_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_finite_reciprocal_mark_vs_count_error_20261122
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m)
    (hMono : Monotone (fun i : ℕ => -(1 / ((i : ℝ) + 1))))
    (hFinite : μ (Ioc 0 T ×ˢ
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) < ⊤)
    (hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
      (Ioc 0 T ×ˢ
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) μ) :
    let B : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : ℕ → Set (ℝ≥0 × ℝ) := fun i => Ioc 0 T ×ˢ
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
    let δ : ℕ → ℝ := fun i =>
      1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    |(∫ p in B, p.2 ∂μ) -
      ∑ i ∈ Finset.Ico n m, c i * (μ (A i)).toReal| ≤
      ∑ i ∈ Finset.Ico n m, δ i * (μ (A i)).toReal := by sorry
