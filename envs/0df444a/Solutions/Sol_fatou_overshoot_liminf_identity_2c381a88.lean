-- Prove2me | solution 1 for fatou_overshoot_liminf_identity_2c381a88
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:23:28.439171+00:00
-- url     : https://prove2.me/submissions/340a5e1e-beb7-4e61-8124-201e935bb734

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_liminf_clock_fatou_without_monotonicity
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
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
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
    (τ : ℕ → Ω → ℝ≥0∞) (hτmeas : ∀ n, Measurable (τ n))
    (hτliminfLowerAE : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) 
    (hσmeas : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => min (ruinTime X x D ω) (τ n ω); ∀ n, Measurable (σ n)))
    : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => min (ruinTime X x D ω) (τ n ω); ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, σ (n + k) ω) = ruinTime X x D ω) := by
    let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => min (ruinTime X x D ω) (τ n ω)
    change ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, σ (n + k) ω) = ruinTime X x D ω
    filter_upwards [hτliminfLowerAE] with ω hω
    let r : ℝ≥0∞ := ruinTime X x D ω
    have htail (n : ℕ) :
        (⨅ k : ℕ, min r (τ (n + k) ω)) =
          min r (⨅ k : ℕ, τ (n + k) ω) := by
      apply le_antisymm
      · apply le_inf
        · exact (iInf_le (fun k : ℕ => min r (τ (n + k) ω)) 0).trans
            (min_le_left r (τ (n + 0) ω))
        · refine le_iInf (fun k => ?_)
          exact (iInf_le (fun j : ℕ => min r (τ (n + j) ω)) k).trans
            (min_le_right r (τ (n + k) ω))
      · refine le_iInf (fun k => ?_)
        exact min_le_min_left r
          (iInf_le (fun j : ℕ => τ (n + j) ω) k)
    calc
      (⨆ n : ℕ, ⨅ k : ℕ, σ (n + k) ω) =
          (⨆ n : ℕ, min r (⨅ k : ℕ, τ (n + k) ω)) := by
            apply iSup_congr
            intro n
            change (⨅ k : ℕ, min r (τ (n + k) ω)) =
              min r (⨅ k : ℕ, τ (n + k) ω)
            exact htail n
      _ = min r (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω) := by
        rw [inf_iSup_eq]
      _ = ruinTime X x D ω := by
        exact min_eq_left hω
end
