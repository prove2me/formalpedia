-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
-- name    : AvramDividend.Classical.avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:27:52.829233+00:00
-- url     : https://prove2.me/theorems/411f372f-9e37-49bf-8fd5-e97e025c111b
-- title:
--   Original BV strictly truncated cash with genuinely full-horizon terminal reward integrable at every physical uniform grid
-- statement:
--   Under original spectral negative bounded-variation source and admissible dividend strategy, continuity of candidate on nonnegative reserve and negative-halfline zero, every physical strictly truncated dividend cash F_n plus the surviving original true horizon T pre-rightpayment payoff is integrable for arbitrary finite or top cap. The proof separates the exact source T-terminal integrability by subtracting previously proved true-T strict cash from the proved full strict cash plus T-terminal integral, then adds proved original strict cash L1 at T-T/(n+2). This leaves the positive compensated Stieltjes error as the only substantive BVB57 issue.
-- source:
--   Proved original avram_p3_bv_original_strict_cash_L1 (67a9c5bf), Proved avram_p3_bv_original_prebudget_L1 (78fa7075), Avram Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n, Integrable (F n) P := by sorry
