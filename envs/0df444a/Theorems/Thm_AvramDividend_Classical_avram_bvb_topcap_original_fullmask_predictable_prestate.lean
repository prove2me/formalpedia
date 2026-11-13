-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_fullmask_predictable_prestate
-- name    : AvramDividend.Classical.avram_bvb_topcap_original_fullmask_predictable_prestate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T10:57:11.393029+00:00
-- url     : https://prove2.me/theorems/07034e37-dbf5-4f8b-9d27-d6d2319a72c6
-- title:
--   Top-cap original strict stopped BV prestate mask predictable including zero reserve and inclusive ruin
-- statement:
--   The original predictable source prepayment reserve mask at nonnegative left-limit surplus, strict start and preterminal cut-off, and inclusive ruin is measurable in the right continuous predictable sigma-algebra when the dividend cap is top.
-- source:
--   Cap-top version of accepted phys48 first projection, using Proved postpayment left limit strongly predictable and inclusive survival strongly predictable.

import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_original_fullmask_predictable_prestate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hCapTop : C = ⊤)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    ∀ n : ℕ,
      let E : Set (ℝ≥0 × Ω) := {p |
        0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
        (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C}
      MeasurableSet[𝓕.rightCont.predictable] E := by sorry
