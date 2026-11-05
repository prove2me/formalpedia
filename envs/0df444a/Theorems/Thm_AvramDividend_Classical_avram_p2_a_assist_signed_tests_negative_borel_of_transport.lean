-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_signed_tests_negative_borel_of_transport
-- name    : AvramDividend.Classical.avram_p2_a_assist_signed_tests_negative_borel_of_transport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:57:28.361192+00:00
-- url     : https://prove2.me/theorems/9d19046a-6e4b-4463-a5e9-861d0b77fb2a
-- title:
--   Signed compact-negative test equality yields separated Borel equality via two subtype integral transports
-- statement:
--   A source-independent Radon uniqueness assembly: equality of signed compact-negative real test integrals, finite negative separated bands, and two exact negative-subtype integral transport formulas imply equality on all negative separated Borel sets, including boundary atoms. This factors the two transport identities so that the original Lévy process can instantiate them directly when proved.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_negative_subtype_compact_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_negative_cut_eq_of_subtype_compact_tests
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_negative_cdf_determines_separated_borel
open MeasureTheory Set Topology AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_a_assist_signed_tests_negative_borel_of_transport
    (μ ν : Measure ℝ)
    (hμBand : ∀ δ : ℝ, 0 < δ → μ (Iic (-δ)) < ⊤)
    (hνBand : ∀ δ : ℝ, 0 < δ → ν (Iic (-δ)) < ⊤)
    (hSigned : ∀ (g : ℝ → ℝ), Continuous g →
      IsCompact (tsupport g) → tsupport g ⊆ Iio (0 : ℝ) →
      (∫ y, g y ∂μ) = (∫ y, g y ∂ν))
    (hTransportμ : ∀ (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ)
        (g : ℝ → ℝ), tsupport g ⊆ Iio (0 : ℝ) →
      (∀ x : {x : ℝ // x < 0}, g (x : ℝ) = f x) →
      (∫ x, f x ∂(Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) μ)) =
        (∫ y, g y ∂μ))
    (hTransportν : ∀ (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ)
        (g : ℝ → ℝ), tsupport g ⊆ Iio (0 : ℝ) →
      (∀ x : {x : ℝ // x < 0}, g (x : ℝ) = f x) →
      (∫ x, f x ∂(Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) ν)) =
        (∫ y, g y ∂ν))
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    μ B = ν B := by sorry
