-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_finitecap_original_single_clock_strict_cash_plus_true_T_budget
-- name    : AvramDividend.Classical.avram_bv_finitecap_original_single_clock_strict_cash_plus_true_T_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T10:20:37.1802+00:00
-- url     : https://prove2.me/theorems/72aa417b-c425-4bf8-ba5b-5e715652853f
-- title:
--   Original finite-cap BV stopped C1 HJB expected cash budget at one strict clock
-- statement:
--   For original bounded-variation spectrally negative Lévy X, any admissible capped dividend D, finite C, strict deterministic s with 0≤s<T, and the original C1 HJB and right-jump premises, the expected discounted genuine dividend payments before s plus the genuine full-horizon surviving prepayment candidate at T is at most w(x). This is the precise single-clock stochastic stopping problem. The physical-grid all-n result follows directly by taking s=T-T/(n+2); there is no spatial cutoff or altered terminal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_finitecap_original_single_clock_strict_cash_plus_true_T_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T) (hFinite : C ≠ ⊤)
    (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) ∂P) ≤ w x := by sorry
