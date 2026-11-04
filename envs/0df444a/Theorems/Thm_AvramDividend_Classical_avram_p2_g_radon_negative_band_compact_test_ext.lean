-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_negative_band_compact_test_ext
-- name    : AvramDividend.Classical.avram_p2_g_radon_negative_band_compact_test_ext
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:13:35.025771+00:00
-- url     : https://prove2.me/theorems/a7d1e6d6-4dc3-49ba-90e3-78bdbbec72c7
-- title:
--   Negative Borel measure uniqueness from finite separated bands and compact continuous tests
-- statement:
--   For two Borel measures on the strictly negative real half-line, finite mass on every band separated from zero guarantees local finiteness and regularity. Equality of real integrals against every compactly supported continuous function then implies equality of measures, including on arbitrary Borel negative marks. This is the missing measure-uniqueness bridge for the original intrinsic Lévy mean-jump identification, conditional only on independently proved compact-test integral identities and finite masses, never on the final Borel rate itself.
-- source:
--   Mathlib.MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure and Measure.ext_of_integral_eq_on_compactlySupported; source-backed local-finiteness helper 9cb44579-41a8-492b-9ed0-27b20dca9a1e; Schilling arXiv:1603.00251 Lemma 9.4(c).

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p2_g_radon_negative_band_compact_test_ext
    (μ ν : Measure {x : ℝ // x < 0})
    (hμBand : ∀ (ε : ℝ), 0 < ε →
      μ {x : {x : ℝ // x < 0} | (x : ℝ) ≤ -ε} < ⊤)
    (hνBand : ∀ (ε : ℝ), 0 < ε →
      ν {x : {x : ℝ // x < 0} | (x : ℝ) ≤ -ε} < ⊤)
    (hTests : ∀ (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ),
      (∫ x, f x ∂μ) = (∫ x, f x ∂ν)) :
    μ = ν := by sorry
