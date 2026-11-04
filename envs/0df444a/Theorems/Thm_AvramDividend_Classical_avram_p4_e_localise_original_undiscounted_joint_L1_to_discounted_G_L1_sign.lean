-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_undiscounted_joint_L1_to_discounted_G_L1_sign
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_undiscounted_joint_L1_to_discounted_G_L1_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:25:11.603497+00:00
-- url     : https://prove2.me/theorems/ded5fb4a-1adb-41ff-af43-c263a3e74e6b
-- title:
--   Original undiscounted true-clock joint L1 yields globally L1 and nonpositive discounted G
-- statement:
--   Combines two independently compiler-accepted P4-E original-source results: exp(-q t) ≤1 for q≥0 transports an actual undiscounted μ×P joint generator residual L1 to discounted joint L1, then Fubini and original HJB give a globally Integrable discounted stopped G on P with G≤0 almost surely. It retains original process/ruin clock/leftLimit and does not assert L1 for martingale M or dividend H.
-- source:
--   Accepted new P4-E 7054fbfc and 41008e2e exact-source bridge and signed G proofs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_clock_discounted_joint_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_discounted_exact_clock_G_L1_nonpositive
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original discounted generator has a globally L¹, nonpositive source residual. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_undiscounted_joint_L1_to_discounted_G_L1_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (n : ℕ) (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (hL1 : Integrable (fun p : ℝ≥0 × Ω =>
      if 0 < p.1 ∧ (p.1 : ℝ≥0∞) <
          min (ruinTime X x D p.2) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
        else 0) (μ.prod P)) :
    Integrable (fun ω =>
      ∫ t : ℝ≥0,
        Real.exp (-(q * (t : ℝ))) * (if 0 < t ∧ (t : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else 0) ∂μ) P ∧
    ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0,
        Real.exp (-(q * (t : ℝ))) * (if 0 < t ∧ (t : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else 0) ∂μ) ≤ 0 := by sorry
