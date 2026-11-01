-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_nojump_past_factor_rightCont
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_nojump_past_factor_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:03:43.301655+00:00
-- url     : https://prove2.me/theorems/b8ae0e83-d179-43be-8b93-01ec7f9fc91b
-- title:
--   Original BV Lévy future no-source-jump event factors from every right-continuous past event
-- statement:
--   Let X be the actual BV finite-negative-activity spectrally negative Lévy process on Ω with its original filtration 𝓕. For every s≤t and every event A measurable under the right-continuous original past 𝓕.rightCont s, P(A ∩ {no actual jumps in (s,t]})=P(A)P({no actual jumps}). This is a genuine source-X conditional void probability precursor to predictable compensation, not merely a constructed Poisson-model independence. It deliberately does not claim the full Poisson count law or kernel compensator.
-- source:
--   On a P-full event, the Proved drift-only interval theorem 2a0cae and monotone residual f6cc show no genuine X jump iff residual increment zero, and the Proved source strict actual jump theorem 7423 supplies the reverse. Rearrange residual increment as source X_t−X_s equals deterministic drift shift. The Proved original independent-increment/right-cont past theorem baf51c16 gives independence of the shifted singleton event from any A in 𝓕.rightCont s, using pinned ProbabilityTheory.Indep_iff. Apply measure_congr for the a.e. event identification under intersection with A, preserving the original Ω, P, 𝓕 and X paths.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_nojump_past_factor_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕.rightCont s) A) :
    P (A ∩ {ω : Ω |
      ∀ u : ℝ≥0, u ∈ Ioc s t →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0}) =
      P A * P {ω : Ω |
        ∀ u : ℝ≥0, u ∈ Ioc s t →
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0} := by sorry
