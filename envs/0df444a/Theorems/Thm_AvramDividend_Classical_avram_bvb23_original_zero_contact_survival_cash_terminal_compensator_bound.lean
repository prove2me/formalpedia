-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_zero_contact_survival_cash_terminal_compensator_bound
-- name    : AvramDividend.Classical.avram_bvb23_original_zero_contact_survival_cash_terminal_compensator_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:25:23.269547+00:00
-- url     : https://prove2.me/theorems/09a9c1c4-2541-423d-ad74-3729ca9a6ee5
-- title:
--   Original BV source zero-contact survival discounted Stieltjes cash plus terminal bounded by full negative-mark compensation
-- statement:
--   On a physical finite-activity BV spectrally negative Levy source trajectory surviving the horizon with original controlled reserve identically zero and no actual negative jumps on the positive-time window, the original Stieltjes discounted cash plus the full-horizon discounted boundary value is bounded by its initial boundary value and the original full negative mark intensity times discounted occupation. The only remaining analytic premise is the exact finite-horizon discount identity; the original source negative-mark kernel is retained. This directly joins Proved original source zero-contact cash 91d1e73f to the corrected survival branch, avoiding false open-interior HJB at reserve zero.
-- source:
--   Proved original source discounted zero-contact cash bound 91d1e73f; real discount identity published as 5ce1f298; exact origin HJB 0344aae3; Avram-Palmowski-Pistorius Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_discounted_cash_le_full_HJB_rate
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb23_original_zero_contact_survival_cash_terminal_compensator_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T)
    (hDiscount : ENNReal.ofReal q * (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) + ENNReal.ofReal (Real.exp (-(q * (T : ℝ)))) = 1) :
    ∀ᵐ ω ∂P,
      (T : ℝ≥0∞) < ruinTime X x D ω →
      (∀ u : ℝ≥0, u ≤ T → riskProcess X x D u ω = 0) →
      (∀ u : ℝ≥0, u ∈ Ioc (0 : ℝ≥0) T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) + ENNReal.ofReal (Real.exp (-(q * (T : ℝ)))) * ENNReal.ofReal (w 0) ≤
      ENNReal.ofReal (w 0) + ENNReal.ofReal (X.ν (Iio (0 : ℝ))).toReal * ENNReal.ofReal (w 0) * (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) := by sorry
