-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b29_BV_finitecap_finite_activity_uniform_signed_cash_source
-- name    : AvramDividend.Classical.avram_b29_BV_finitecap_finite_activity_uniform_signed_cash_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T15:16:59.747522+00:00
-- url     : https://prove2.me/theorems/b3b511ca-aac5-456a-83e4-fff386f5bc26
-- title:
--   Original finite-cap finite-jump-activity BV signed physical source on the explicit strictly pre-horizon uniform cofinal clock
-- statement:
--   Construct exactly the original finite-cap BV signed physical source with all standing HJB and dividend assumptions, finite jump activity, and the fixed real physical strict cofinal clock u_n=T−T/(n+2). The remaining existential witnesses are integrable nonpositive-mean signed gains R+J and vanishing L1 positive cash residual Err, preserving actual strict Iio dividend cash and terminal survival value. This isolates the substantive signed Itô–Stieltjes and compensated-jump source on a canonical finite-activity physical grid; the deterministic cofinal clock conditions have already been Proved by avram_bv_strict6_original_physical_prefix_cofinal_clock.
-- source:
--   Prove2Me finiteactivity B29 source fd611942 and proved deterministic physical cofinal clock b4799e97; exact original physical finite-activity cash source, 15 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_b29_BV_finitecap_finite_activity_uniform_signed_cash_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (hwpos : 0 < w x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let u : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
    ∃ R J Err : ℕ → Ω → ℝ,
        (∀ n, Integrable (fun ω => R n ω + J n ω) P ∧
          (∫ ω, R n ω + J n ω ∂P) ≤ 0) ∧
        (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
        Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P)
          atTop (𝓝 (0 : ℝ)) ∧
        (∀ n, ∀ᵐ ω ∂P,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
           else 0) ≤
            w x + (R n ω + J n ω) + max (Err n ω) 0)  := by sorry
