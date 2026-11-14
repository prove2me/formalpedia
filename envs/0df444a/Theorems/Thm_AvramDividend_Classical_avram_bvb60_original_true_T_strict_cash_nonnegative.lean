-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb60_original_true_T_strict_cash_nonnegative
-- name    : AvramDividend.Classical.avram_bvb60_original_true_T_strict_cash_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:19:20.133237+00:00
-- url     : https://prove2.me/theorems/8b6bc585-d44c-4618-9093-d78c24a1304a
-- title:
--   Original strict physical discounted cash plus true full-horizon surviving reward is nonnegative pointwise
-- statement:
--   With exactly the original dividendMeasure, paymentTimes, strict uniform grid, actual ruinTime and full-horizon postpayment terminal reserve, the finite-horizon cash F_n is pointwise nonnegative under source nonnegative candidate value on the pre-ruin region; the dividend part is an ENNReal integral converted to a nonnegative real.
-- source:
--   Avram Prop 4(i) nonnegative candidate and original physical strict cash source, source BVB54/BVB55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb60_original_true_T_strict_cash_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q T : ℝ) (hT : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n ω, 0 ≤ F n ω := by sorry
