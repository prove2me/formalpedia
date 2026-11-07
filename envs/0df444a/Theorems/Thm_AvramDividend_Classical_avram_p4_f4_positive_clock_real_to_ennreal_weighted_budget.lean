-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_positive_clock_real_to_ennreal_weighted_budget
-- name    : AvramDividend.Classical.avram_p4_f4_positive_clock_real_to_ennreal_weighted_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:34:12.012401+00:00
-- url     : https://prove2.me/theorems/ec222d84-9f8c-4f4a-844d-16bf102a0874
-- title:
--   Real stopped event budget converts to exact probability-weighted ENNReal budget
-- statement:
--   For a genuine probability measure and an almost-everywhere nonnegative integrable real reward, a finite real expectation upper bound on any measurable stopped event yields the original probability-weighted ENNReal lintegral bound over precisely the same event. This reduces the original mixed Lévy source budget to one real conditional expectation plus its stochastic source construction.
-- source:
--   Use proved avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget on the restricted measure and pinned ENNReal ofReal multiplication/cast identities. No Lévy source assumptions are changed.

import Mathlib
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_positive_clock_real_to_ennreal_weighted_budget
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (S : Set Ω) (F : Ω → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hFI : Integrable F P)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hMeanS : (∫ ω in S, F ω ∂P) ≤ B * (P S).toReal) :
    (∫⁻ ω in S, ENNReal.ofReal (F ω) ∂P) ≤
      ENNReal.ofReal B * P S := by sorry
