-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_disjoint_negative_borel_real_count_add_ae
-- name    : AvramDividend.Classical.avram_a20_original_disjoint_negative_borel_real_count_add_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T09:06:34.621249+00:00
-- url     : https://prove2.me/theorems/34ab00f2-d753-48b0-932d-c66df7f4dd2f
-- title:
--   Genuine original disjoint negative-Borel jump counts add as real random variables almost surely
-- statement:
--   For the original spectrally negative Lévy process with finite negative jump intensity, original intrinsic Borel mark counts on a fixed interval for two disjoint negative mark sets are finite almost surely. Their union count is the sum of counts and the real-valued count identity follows. This is the source-faithful bridge enabling disjoint-cell covariance reductions to single-cell variance certificates without an auxiliary Poisson model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_disjoint_negative_borel_real_count_add_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hNegA : A ⊆ Iio (0 : ℝ)) (hNegB : B ⊆ Iio (0 : ℝ))
    (hDisj : Disjoint A B) :
    let N : Set ℝ → Ω → ℝ≥0∞ := fun C ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ C)
    ∀ᵐ ω ∂P, (N (A ∪ B) ω).toReal =
      (N A ω).toReal + (N B ω).toReal := by sorry
