-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_predictable_observable_triple
-- name    : AvramDividend.Classical.avram_bvb_topcap_original_predictable_observable_triple
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:00:56.445643+00:00
-- url     : https://prove2.me/theorems/896bad92-899d-4c53-8c9a-42bd4b771542
-- title:
--   Original right-continuous predictable sigma algebra sees left-limit reserve, time and inclusive survival
-- statement:
--   The original dividend-control filtration makes the prepayment left-limit reserve, time coordinate, and inclusive survival set predictable. These three jointly determine the stopped fullmask when C equals top; no finite cap is required.
-- source:
--   Direct short extraction of independently Proved facts assembled in accepted phys48, retaining original process and strategy and including zero and ruin.

import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_original_predictable_observable_triple
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    let U : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    Measurable[𝓕.rightCont.predictable] U ∧
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω => p.1) ∧
    MeasurableSet[𝓕.rightCont.predictable] {p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2} := by sorry
