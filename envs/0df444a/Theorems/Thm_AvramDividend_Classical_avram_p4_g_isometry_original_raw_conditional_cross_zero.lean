-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_conditional_cross_zero
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_raw_conditional_cross_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:23:21.805928+00:00
-- url     : https://prove2.me/theorems/18ad8d66-e0b0-42b3-8e6e-1a8089de5644
-- title:
--   Original raw-filtration predictable L2 past coefficient is orthogonal to a centred future increment
-- statement:
--   For the given original Lévy filtration F, an L2 past coefficient measurable at raw time t is orthogonal to an L2 future increment whose conditional expectation given that same raw F_t is zero. This is the exact off-diagonal Hilbert-space step required after original intrinsic finite-band count centring; it does not assume usual conditions, replace the source Poisson model, or claim diagonal second moments. Conditional centring is explicit and may be discharged by the P4-G original rectangle-law bridge.
-- source:
--   Pinned condExp_mul_of_stronglyMeasurable_left and integral_condExp for 𝓕.le t, adapted with source filtration index from proved P4-B rightCont case, which does not cover raw source index.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_g_isometry_original_raw_conditional_cross_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (F G : Ω → ℝ)
    (hF : StronglyMeasurable[𝓕 t] F)
    (hFl2 : MemLp F 2 P) (hGl2 : MemLp G 2 P)
    (hGcentred : P[G | 𝓕 t] =ᵐ[P] 0) :
    (∫ ω, F ω * G ω ∂P) = 0 := by sorry
