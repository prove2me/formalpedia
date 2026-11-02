-- Prove2me | solution 1 for fatou_liminf_nonmonotone_pointwise_upper_bound_a302087d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:55:16.374099+00:00
-- url     : https://prove2.me/submissions/7814e011-9430-47c0-afaa-d207c6060fc1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω) = ruinTime X x D ω)
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) 
    (hσmeas : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω; ∀ n, Measurable (σ n)))
    (hσmono : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω; ∀ ω, Monotone (fun n => σ n ω)))
    (hσsupAE : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω; ∀ᵐ ω ∂P, (⨆ n, σ n ω) = ruinTime X x D ω))
    (hσle : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω; ∀ n ω, σ n ω ≤ τ n ω))
    : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω; ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) := by
    classical
    let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω
    change ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)
    intro n
    calc
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
            apply lintegral_mono
            intro ω
            apply lintegral_mono_set
            intro t ht
            have hs : paymentTimes (σ n ω) ⊆ paymentTimes (τ n ω) := by
              simpa using paymentTimes_min_mono_horizon
                ⊤ (σ n ω) (τ n ω) (hσle n ω)
            exact ⟨hs ht.1, ht.2⟩
      _ ≤ ENNReal.ofReal (w x) := hBudget n
end
