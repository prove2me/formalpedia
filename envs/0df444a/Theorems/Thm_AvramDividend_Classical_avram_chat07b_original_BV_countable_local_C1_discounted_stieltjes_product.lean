-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_countable_local_C1_discounted_stieltjes_product
-- name    : AvramDividend.Classical.avram_chat07b_original_BV_countable_local_C1_discounted_stieltjes_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:07:34.044799+00:00
-- url     : https://prove2.me/theorems/d3f9952c-1393-4848-80cd-06cb61c5559d
-- title:
--   One original BV Lévy almost-sure event satisfies every countably localised discounted C1 Stieltjes product rule
-- statement:
--   For the unchanged original Standing finite-variation SpectrallyNegativeLevy source X and original adapted dividend D, the discounted Stieltjes integration-by-parts product of the actual clipped post-payment reserve composed with a C1 HJB test holds on one common P-almost-sure event simultaneously for any countable collection of compact interior reserve bands and all stopping horizons, conditional on literal path containment. It keeps simultaneous jumps in the actual post-payment path. The Ioc product starts after the left endpoint and therefore does not claim to include the distinct physical time-zero dividendMeasure atom.
-- source:
--   Avram Proposition 4(i), original stopped BV C1 finite-variation source, accepted single-band Ioc discounted Stieltjes product 921f2ec5 and pinned ae_all_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_local_C1_discounted_stieltjes_product
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_chat07b_original_BV_countable_local_C1_discounted_stieltjes_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (cap : ℝ)
    (lo hi : ℕ → ℝ)
    (hBand : ∀ n, lo n < hi n)
    (hInside : ∀ n, Icc (lo n) (hi n) ⊆ Ioo 0 cap)
    (hwC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ T : ℝ≥0,
      (∀ t : ℝ≥0,
        x + X.X (min t T) ω - rightLimit D (min t T) ω ∈
          Icc (lo n) (hi n)) →
      let f : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ))
      let g : ℝ≥0 → ℝ := fun t =>
        w (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hf : BoundedVariationOn f Set.univ,
        ∃ hg : BoundedVariationOn g Set.univ,
          ∀ a b : ℝ≥0, a ≤ b →
            (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
              Function.rightLim f b • Function.rightLim g b -
              Function.rightLim f a • Function.rightLim g a -
              (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by sorry
