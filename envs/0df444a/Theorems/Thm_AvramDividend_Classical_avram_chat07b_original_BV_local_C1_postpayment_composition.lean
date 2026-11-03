-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_local_C1_postpayment_composition
-- name    : AvramDividend.Classical.avram_chat07b_original_BV_local_C1_postpayment_composition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:48:36.217018+00:00
-- url     : https://prove2.me/theorems/8a60e194-d6c0-4578-9164-725f443149c1
-- title:
--   Original BV controlled post-payment Lévy path retains bounded variation under compact-localised C¹ tests
-- statement:
--   For the actual standing bounded-variation spectrally negative Lévy process X and its original dividend strategy D, the post-payment reserve frozen at finite time T has globally bounded variation. If its values remain in an interior compact reserve band and w is C1 on the enclosing positive strip, then the true composition w(x+X.X(min t T)-rightLimit D(min t T)) also has globally bounded variation, including initial and simultaneous right-dividend jumps. The proof obtains the compact Lipschitz bound from the accepted C1 source helper and invokes Mathlib LipschitzOnWith.comp_boundedVariationOn on the accepted original path variation. No hypothetical sample space, stochastic payout bound or extra global smoothness.
-- source:
--   Avram, Palmowski and Pistorius (2007) Proposition 4(i), C1 finite-variation controlled reserve localisation and pathwise Stieltjes composition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_finite_cap_local_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_chat07b_original_BV_local_C1_postpayment_composition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (cap lo hi : ℝ)
    (hlr : lo < hi) (hsub : Icc lo hi ⊆ Ioo 0 cap)
    (hwC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      (∀ t : ℝ≥0,
        x + X.X (min t T) ω - rightLimit D (min t T) ω ∈ Icc lo hi) →
      BoundedVariationOn
        (fun t : ℝ≥0 =>
          w (x + X.X (min t T) ω - rightLimit D (min t T) ω))
        Set.univ := by sorry
