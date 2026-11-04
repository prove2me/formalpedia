-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_clock_generator_joint_L1_to_G_L1
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_generator_joint_L1_to_G_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:47:15.359444+00:00
-- url     : https://prove2.me/theorems/d5d4cfc6-9637-4383-b8c1-41d1f014e33f
-- title:
--   Original exact ruin-clipped predictable generator joint physical L1 yields true probability-space G integrability
-- statement:
--   For the actual source X, D and natural ruin truncation min(ruinTime,n), if the genuine discounted source generator-minus-q drift is Integrable on a physical-time measure μ times the ORIGINAL probability measure P, its pathwise physical-time integral G is Integrable P. This is a valid Fubini L1 upgrade, not an invocation of optional stopping or a claim that local pathwise integrability suffices. An explicit joint L1 input is required, supplied on compact predictable source windows by existing source 1829a383 or 732738fd under its premises. SFinite P and μ are explicit Mathlib measure instances.
-- source:
--   Pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: MeasureTheory.Integrable.integral_prod_right; original finite clock 6b7a13a0 and source generator 1829a383.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine joint original physical generator L¹ gives L¹ of its stopped path-integrated residual. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_generator_joint_L1_to_G_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (n : ℕ)
    (μ : Measure ℝ≥0) [SFinite μ]
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
        else 0 ∂μ) P := by sorry
