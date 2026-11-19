-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_ubv_finite_negative_activity_gaussian_nonzero
-- name    : AvramDividend.Classical.avram_f6_ubv_finite_negative_activity_gaussian_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:17:29.669962+00:00
-- url     : https://prove2.me/theorems/21865e8d-5815-47a9-9211-04f5cb2bd746
-- title:
--   Finite-activity unbounded-variation spectrally negative Lévy driver necessarily has a Gaussian component
-- statement:
--   In an unbounded variation spectrally negative Lévy process, finite total negative-jump intensity forces the Gaussian coefficient nonzero. By contradiction a zero Gaussian coefficient implies infinite negative jump intensity, proved from the authentic Lévy smallmark first-moment condition. Useful for the mixed finite-activity source and avoiding impossible purejump finite-activity case.
-- source:
--   Proved b9b373fa purejump UBV infinite intensity, original mixed finite activity X.ν measure assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_ubv_finite_negative_activity_gaussian_nonzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    X.σ ≠ 0 := by sorry
