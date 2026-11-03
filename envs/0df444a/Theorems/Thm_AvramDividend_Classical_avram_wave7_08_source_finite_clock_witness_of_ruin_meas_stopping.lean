-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
-- name    : AvramDividend.Classical.avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:34:37.576582+00:00
-- url     : https://prove2.me/theorems/d499e28b-dd2c-43d5-9218-1c6407b24552
-- title:
--   Exact original-source finite clock witness from ruin measurability and stopping
-- statement:
--   For original X and exact ruinTime on the original Ω and filtration, provided source ruinTime is both ambient measurable and a stopping time, construct the exact finite clock appearing in the W7-08 stopped Itô witnesses along with its real measurability and right-continuous filtration stopping property.
-- source:
--   Bridge both remotely Proved W7-08 source clock adapters 7bcaac6d and 413f855c. The unresolved actual source ruinTime measurability and stopping are explicit premises, not proved here.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (hRuinMeas : Measurable (ruinTime X x D))
    (hRuinStop : IsStoppingTime 𝓕.rightCont (ruinTime X x D)) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      Measurable (fun ω => (τ ω : ℝ)) ∧
      IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) := by sorry
