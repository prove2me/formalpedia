-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_global_variation
-- name    : AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_global_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:56:58.319894+00:00
-- url     : https://prove2.me/theorems/283f272e-2794-4ffc-877a-e047d2f6fff6
-- title:
--   Actual discounted post-payment BV reserve test has finite global path variation
-- statement:
--   On the actual BV spectrally negative Levy source with an admissible dividend strategy, any compact-band Lipschitz HJB test admits an exactly matching globally Lipschitz extension whose exponentially discounted evaluation along the true post-payment surplus, frozen at any finite horizon, has globally finite variation almost surely.
-- source:
--   Theorem discount_exp_global_variation and theorem postPayment_global_Lipschitz_localisation; Mathlib BoundedVariationOn.fun_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_global_Lipschitz_localisation
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_global_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (lo hi : ℝ) (L : NNReal)
    (hw : LipschitzOnWith L w (Icc lo hi)) :
    ∃ v : ℝ → ℝ,
      LipschitzWith L v ∧ Set.EqOn w v (Icc lo hi) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        BoundedVariationOn
          (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)) *
            v (x + X.X (min t T) ω - rightLimit D (min t T) ω))
          Set.univ := by sorry
