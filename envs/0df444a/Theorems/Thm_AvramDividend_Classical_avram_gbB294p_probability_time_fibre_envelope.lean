-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB294p_probability_time_fibre_envelope
-- name    : AvramDividend.Classical.avram_gbB294p_probability_time_fibre_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:19:01.436698+00:00
-- url     : https://prove2.me/theorems/e4a60cb0-e3ec-42ef-83ad-193e9c4ea0b1
-- title:
--   Probability-time measurable fibres bound the product occupation mass
-- statement:
--   For a probability measure P and Lebesgue time, the product measure of a measurable occupation set S is bounded by the integral of any pointwise upper envelope for its P-measure time fibres. Probability supplies the finite/σ-finite hypothesis required for the standard Tonelli theorem; unlike the unrestricted B294 statement, the formalised s-finiteness is explicit and source-sound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_gbB294p_probability_time_fibre_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by sorry
