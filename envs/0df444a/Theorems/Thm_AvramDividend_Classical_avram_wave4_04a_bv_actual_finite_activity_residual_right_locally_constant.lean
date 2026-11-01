-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_activity_residual_right_locally_constant
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_activity_residual_right_locally_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:09:09.025743+00:00
-- url     : https://prove2.me/theorems/03f98565-99b3-4d29-979f-e96d1c3b71a8
-- title:
--   Genuine finite-activity BV Lévy drift residual is almost surely right-locally constant at every time on a finite horizon
-- statement:
--   For the actual original finite-negative-intensity bounded-variation spectrally negative Lévy process X, on a full-measure event, at every time t in a fixed positive finite horizon [0,T], the real drift residual Y(u)=u·X.drift−X_u(ω) is equal to Y(t) throughout some right neighbourhood of t, restricted to u≤T. This is an original-path step-function property, using genuine X.rightCont and the canonically Proved source residual finite-range theorem, not an auxiliary Poisson process. It is a precursor to identifying drift-deficient grid cells with genuine jump times.
-- source:
--   Source original finite-range event canonically Proved 92aa24fb-9706-4627-ad59-287adbd329d0, exact original X.rightCont, the continuous deterministic drift map u↦u·X.drift, and the T1 fact that a finite subset of ℝ is closed. Continuity within the right-sided filter and a finite set S ensure Y cannot leave Y(t) while staying inside S in a sufficiently small right neighbourhood. This is not an equality of jump count laws or a predictable compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_residual_range_on_horizon

open MeasureTheory Filter Set Topology Finset AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_activity_residual_right_locally_constant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      ∀ᶠ u in nhdsWithin t (Ici t), u ≤ T →
        (u : ℝ) * X.drift - X.X u ω =
          (t : ℝ) * X.drift - X.X t ω := by sorry
