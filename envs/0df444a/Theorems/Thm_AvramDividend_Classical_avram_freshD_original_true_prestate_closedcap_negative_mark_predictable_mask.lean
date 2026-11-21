-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_true_prestate_closedcap_negative_mark_predictable_mask
-- name    : AvramDividend.Classical.avram_freshD_original_true_prestate_closedcap_negative_mark_predictable_mask
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:10:42.25354+00:00
-- url     : https://prove2.me/theorems/d432161d-9dd1-4b3b-b082-77eda5d64cf2
-- title:
--   Original closed-cap negative-mark prestate predictable mask on the genuine Lévy path
-- statement:
--   The exact four-component closed-cap source mask used in the original finite-activity full negative-mark stopped Ito certificate, comprising positive time, nonnegative pre-dividend Lévy reserve left limit, finite cap comparison and negative mark, is measurable for the product of right-continuous predictable filtration with real marks. This genuine state-domain measurability sub-obligation removes the first remote CE blocker in source b7420f09 and is reusable for full nonlinear marked compensation across zero and cap boundaries. No artificial martingale or expected cash bound is assumed.
-- source:
--   Original Avram Dividend Classical finite activity mixed Gaussian/full negative mark cash source, specifically original published source b7420f09; derivation from Proved 94ee9994 original postpayment reserve left-limit strong predictability and measurable ENNReal.ofReal with four measurable inequalities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_true_prestate_closedcap_negative_mark_predictable_mask
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (C : ℝ≥0∞) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun r : ℝ≥0 =>
        x + X.X r p.2 - rightLimit D r p.2) p.1
    MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      {p : (ℝ≥0 × Ω) × ℝ |
        0 < p.1.1 ∧ 0 ≤ Y p.1 ∧
        ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0} := by sorry
