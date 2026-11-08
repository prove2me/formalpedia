-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn10_positive_clock_allcap_five_signed_witnesses
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn10_positive_clock_allcap_five_signed_witnesses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T23:35:25.988115+00:00
-- url     : https://prove2.me/theorems/314938eb-fd3d-4552-8615-68f276116d74
-- title:
--   Positive-clock conditional expected upper bound yields five centred signed witnesses without cap finiteness
-- statement:
--   For an integrable exact stopped reward and a measurable zero-clock event, a strictly positive-clock probability-weighted expected upper bound supplies the five centred martingale and nonpositive-residual witnesses used in the original pure-jump and mixed Lévy finite-clock budgets. The zero-clock branch is masked to the initial benchmark; no finite-cap assumption is needed, and the proof does not alter the underlying Lévy process or dividend strategy.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn10_clock_partition_mean_upper

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn10_positive_clock_allcap_five_signed_witnesses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (b : ℝ) (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hzeroMeas : MeasurableSet {ω : Ω | σ ω = 0})
    (hFI : Integrable F P)
    (hpositive : (∫ ω in {ω : Ω | σ ω ≠ 0}, F ω ∂P) ≤
      b * (P {ω : Ω | σ ω ≠ 0}).toReal) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        (if σ ω = 0 then b else F ω) ≤
          b + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
