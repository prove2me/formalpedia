-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_anycap_finite_mesh_full_stieltjes_nonpositive
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_anycap_finite_mesh_full_stieltjes_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:44:12.223002+00:00
-- url     : https://prove2.me/theorems/f00c1d66-72b3-4b75-857a-2dcc95435998
-- title:
--   Finite mesh of genuine original dividend payments has nonpositive full cap-Stieltjes correction
-- statement:
--   For each finite indexed source-frozen (a_i,b_i] dividend payment cell of an admissible original control, with b_i in the genuine original ruin paymentTimes, prove that the sum of exact real Stieltjes cell cash masses and corresponding cap-extended value variations is nonpositive. The source theorem handles both absolutely/singular continuous mass and the right-payment atom, including boundary contact at zero and upper cap. This establishes finite-mesh deterministic control contribution without making an unproved stochastic chain-rule or limiting assertion, and initial payments are handled separately.
-- source:
--   Proved P4-D original every payment Stieltjes cell budget c04d2cd0; original dividendMeasure Ioc; Avram-Palmowski-Pistorius Proposition 4(i), Eq (5.13)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_anycap_true_payment_full_stieltjes_cell_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_anycap_finite_mesh_full_stieltjes_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (s : Finset ι) (a b : ι → ℝ≥0)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hPay : ∀ i ∈ s, (b i : ℝ) ∈ paymentTimes (ruinTime X x D ω)) :
    (∑ i ∈ s, ((dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))).toReal +
      V (x + X.X (b i) ω - rightLimit D (b i) ω) -
      V (x + X.X (b i) ω - rightLimit D (a i) ω))) ≤ 0 := by sorry
