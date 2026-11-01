-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_drift_residual_strict_interval_iff_jump
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_drift_residual_strict_interval_iff_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:54:15.012533+00:00
-- url     : https://prove2.me/theorems/d775f040-013e-459c-957a-68cfcabe2e0e
-- title:
--   Original BV source drift-deficit intervals are exactly the time intervals containing genuine X jumps
-- statement:
--   Under original-source BV finite-negative-intensity hypotheses, a single probability-one event covers every subinterval (s,t] of a finite horizon. The true residual d·t−X_t increases strictly over (s,t] if and only if that same original path has at least one nonzero source X jump in (s,t]. This provides both directions of the previously missing exact grid-cell indicator versus genuine jump-set bridge: a strictly drift-deficient cell cannot be caused by a hidden diffuse residual component. Neither a constructed Lévy process nor its sample space is used. A further finite-jump separation lemma is still needed for equality of entire grid active-cell counts and the source Poisson law.
-- source:
--   Original no-jump source drift-only interval theorem (publication pending at specification time), original monotone residual f6cc1059-e8ca-403e-8d73-71a139d3dc4c Proved, strict residual jump iff actual X jump 7423dfee-c973-497f-a274-07e572cbd7a0 Proved, pinned Monotone.le_leftLim. If no jump, source drift-only theorem forces equal residual endpoints; if genuine jump u lies inside, monotonicity gives Y_s≤Y_{u-}<Y_u≤Y_t. Needs exact Proved import confirmation before publication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_drift_residual_strict_interval_iff_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      ((s : ℝ) * X.drift - X.X s ω <
          (t : ℝ) * X.drift - X.X t ω ↔
        ∃ u : ℝ≥0, u ∈ Ioc s t ∧
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) := by sorry
