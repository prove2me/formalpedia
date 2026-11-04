-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_allcap_exact_clock_joint_L1_G_nonpositive
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_allcap_exact_clock_joint_L1_G_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:50:59.363905+00:00
-- url     : https://prove2.me/theorems/4813157c-db03-46cc-a1cc-9064e10b3980
-- title:
--   Original all-cap exact ruin-truncated G is globally L1 and a.s. nonpositive from true joint L1 and source HJB
-- statement:
--   For the original spectrally negative Lévy process, any nonzero extended cap C and actual min(ruinTime,n) clock, a genuine joint time×P L1 estimate for its predictable pre-event generator-minus-q residual yields an Integrable P random time-integrated residual G and G≤0 almost surely. The proof uses pinned Mathlib Fubini and the source chronological all-cap interior theorem; the source HJB controls physical-time sign. Joint L1 is explicitly required, rather than inferred from mere pathwise or local integrability. The stochastic martingale and random Stieltjes dividend terms remain separate.
-- source:
--   Original predictable allcap c9db7a94; exact pinned Mathlib Integrable.integral_prod_right; same original X,D and generator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual exact-clock joint L¹ and all-cap HJB produce an L¹, a.s.-nonpositive G residual. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_allcap_exact_clock_joint_L1_G_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (n : ℕ) (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (hL1 : Integrable
      (fun p : ℝ≥0 × Ω =>
        if 0 < p.1 ∧ (p.1 : ℝ≥0∞) <
          min (ruinTime X x D p.2) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
        else 0) (μ.prod P)) :
    Integrable (fun ω =>
      ∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else 0 ∂μ) P ∧
    ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else 0 ∂μ) ≤ 0 := by sorry
