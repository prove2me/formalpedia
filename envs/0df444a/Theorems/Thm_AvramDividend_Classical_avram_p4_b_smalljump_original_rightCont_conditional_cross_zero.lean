-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_conditional_cross_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_conditional_cross_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:44:10.990607+00:00
-- url     : https://prove2.me/theorems/af5f9530-e0a4-4689-832a-c3862734afca
-- title:
--   Source right-continuous filtration: conditional L² cross-moment cancellation
-- statement:
--   For the original spectrally negative Lévy process P, a source-right-continuous-time-measurable square-integrable coefficient F is orthogonal in L² to a square-integrable random variable G with zero conditional expectation given the source filtration at the same time. This applies to actual future compensated jump increments after P2 proves their centring; the centring remains an explicit hypothesis.
-- source:
--   Mathlib conditional-expectation pull-out and integral identity; original right-continuous filtration, adapted from the accepted 6d7721ef orthogonality proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_conditional_cross_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (F G : Ω → ℝ)
    (hF : StronglyMeasurable[𝓕.rightCont t] F)
    (hFl2 : MemLp F 2 P) (hGl2 : MemLp G 2 P)
    (hGcentred : P[G | 𝓕.rightCont t] =ᵐ[P] 0) :
    (∫ ω, F ω * G ω ∂P) = 0 := by sorry
