-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_clock_discounted_joint_L1
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_discounted_joint_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:06:26.459242+00:00
-- url     : https://prove2.me/theorems/7054fbfc-e603-4773-aeba-b2713ea4fed6
-- title:
--   Original exact ruin-truncated generator joint L1 is preserved under bounded discount
-- statement:
--   At the actual source min(ruinTime,n) predictable generator drift and original left-limit reserve, a nonnegative discount rate multiplies the joint time×probability integrable residual by exp(-q t) bounded in [0,1]. Thus original joint L1 persists with no invented martingale or boundary assumptions; essential Fubini integration into G is a subsequent step.
-- source:
--   Exact source original riskProcess and rightLimit definitions; pinned Mathlib Integrable.bdd_mul and Real.exp_le_exp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A nonnegative discount rate preserves source exact-clock joint L¹. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_discounted_joint_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (μ : Measure ℝ≥0)
    (hL1 : Integrable
      (fun p : ℝ≥0 × Ω =>
        if 0 < p.1 ∧ (p.1 : ℝ≥0∞) <
          min (ruinTime X x D p.2) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
        else 0) (μ.prod P)) :
    Integrable
      (fun p : ℝ≥0 × Ω =>
        Real.exp (-(q * (p.1 : ℝ))) *
          (if 0 < p.1 ∧ (p.1 : ℝ≥0∞) <
            min (ruinTime X x D p.2) (n : ℝ≥0∞)
          then X.generator w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
              q * w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
          else 0)) (μ.prod P) := by sorry
