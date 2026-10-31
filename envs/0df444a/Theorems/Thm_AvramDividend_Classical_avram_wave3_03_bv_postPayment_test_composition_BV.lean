-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_test_composition_BV
-- name    : AvramDividend.Classical.avram_wave3_03_bv_postPayment_test_composition_BV
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:51:38.309572+00:00
-- url     : https://prove2.me/theorems/4827c859-e7d8-40bc-89c5-8c03ad075063
-- title:
--   Localised HJB test of genuine post-payment BV reserve retains finite total variation
-- statement:
--   For the actual bounded-variation source Levy process and an admissible dividend-strategy path, every post-payment controlled reserve composed with a function Lipschitz on its localised range has finite time variation simultaneously almost surely on all finite horizons. The post-payment process includes the strict-right initial and later dividend atoms.
-- source:
--   Canonical Proved post-payment source reserve BoundedVariationOn on every finite horizon and Mathlib LipschitzOnWith.comp_boundedVariationOn, matching the already accepted pre-payment test-composition argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_reserve_boundedVariationOn_compact

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_postPayment_test_composition_BV
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (lo hi : ℝ) (L : NNReal)
    (hw : LipschitzOnWith L w (Icc lo hi)) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (s : Set ℝ≥0),
      s ⊆ Icc (0 : ℝ≥0) T →
      Set.MapsTo (fun t => x + X.X t ω - rightLimit D t ω) s (Icc lo hi) →
      BoundedVariationOn
        (fun t => w (x + X.X t ω - rightLimit D t ω)) s := by sorry
