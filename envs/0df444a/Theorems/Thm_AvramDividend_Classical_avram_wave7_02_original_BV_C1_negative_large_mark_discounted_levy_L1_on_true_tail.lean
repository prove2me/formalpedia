-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_negative_large_mark_discounted_levy_L1_on_true_tail
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_negative_large_mark_discounted_levy_L1_on_true_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:27:22.08013+00:00
-- url     : https://prove2.me/theorems/899e9e1d-1359-4e7b-ba03-3d2145cf0534
-- title:
--   Original BV C1 controlled large negative jump nonlinear discounted kernel is absolutely integrable on its finite Levy tail
-- statement:
--   For actual original spectrally negative Levy X, any finite true mark intensity on the separated negative tail (-∞,-a/2] and bounded candidate w on reserves at most b give absolute L1 of the original discounted controlled left-reserve C1 nonlinear jump kernel, even when marks overshoot ruin. The explicit measurability hypothesis is independent. Combines the original-source value bound with the true physical Levy finite-tail mass and does not rely on C2 or a copied Poisson process.
-- source:
--   W7-02 large-mark candidate uniform bound e44668f8 and true source Levy tail mass; intended to join accepted small-mark L1 f827dbd6 over (-a/2,0) for the complete BV C1 compensation kernel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_negative_large_mark_discounted_levy_L1_on_true_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b R : ℝ) (ha : 0 < a) (hab : a ≤ b) (hR : 0 ≤ R)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (hMeas : AEStronglyMeasurable (fun z : ℝ =>
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t + z) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t)))
      (X.ν.restrict (Iic (-a / 2)))) :
    IntegrableOn (fun z : ℝ =>
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t + z) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t)))
      (Iic (-a / 2)) X.ν := by sorry
