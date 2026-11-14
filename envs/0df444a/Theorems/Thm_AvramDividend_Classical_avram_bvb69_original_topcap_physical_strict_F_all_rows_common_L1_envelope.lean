-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb69_original_topcap_physical_strict_F_all_rows_common_L1_envelope
-- name    : AvramDividend.Classical.avram_bvb69_original_topcap_physical_strict_F_all_rows_common_L1_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:48:00.931131+00:00
-- url     : https://prove2.me/theorems/6d2cd496-5eed-4fe0-80a3-bc0204931aa0
-- title:
--   Original physical uniform strict dividend cash with genuine full-T survival payoff has one L1 majorant for all meshes
-- statement:
--   Under original BV admissible strategy, candidate w continuous on nonnegative reserve, vanishing below zero and nonnegative before ruin, the exact discounted strict cash to T−T/(n+2) plus original full-T survivor reward F_n has a common integrable majorant for all physical uniform mesh indices n. Choose the full horizon strict cash plus the identical true-T survivor reward as the majorant. Uses original dividendMeasure, paymentTimes, ruinTime and riskProcess at actual S; no premature payoff substitution.
-- source:
--   Proved p3 BV full-T strict cash+survival prebudget L1 78fa7075, exact original uniform physical cash a.e. monotonicity c5eeb765 and strict horizon convergence 670d403d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb69_original_topcap_physical_strict_F_all_rows_common_L1_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∃ G : Ω → ℝ, Integrable G P ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ G ω := by sorry
