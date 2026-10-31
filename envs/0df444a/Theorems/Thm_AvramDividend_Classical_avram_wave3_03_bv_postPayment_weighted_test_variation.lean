-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_weighted_test_variation
-- name    : AvramDividend.Classical.avram_wave3_03_bv_postPayment_weighted_test_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:39:16.173415+00:00
-- url     : https://prove2.me/theorems/c611b942-4d9d-4d63-96d1-a051ea9f45a4
-- title:
--   Time-weighted HJB test along actual post-payment BV reserve has localised bounded variation
-- statement:
--   Every time-discount weight having bounded variation on compact time intervals multiplies the locally Lipschitz test function of the actual post-payment bounded-variation controlled Levy reserve without destroying locally bounded variation. The theorem preserves all continuous and atomic controlled dividend components, including the initial payment, under sample-path localisation.
-- source:
--   Apply the previously Proved original-source post-payment test composition theorem (4827c859-e7d8-40bc-89c5-8c03ad075063) and Mathlib.Analysis.BoundedVariation.BoundedVariationOn.fun_mul, verified in the pinned Mathlib index.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_test_composition_BV

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_postPayment_weighted_test_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (lo hi : ℝ) (L : NNReal)
    (hw : LipschitzOnWith L w (Icc lo hi))
    (d : ℝ≥0 → ℝ)
    (hd : ∀ T : ℝ≥0, BoundedVariationOn d (Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (s : Set ℝ≥0),
      s ⊆ Icc (0 : ℝ≥0) T →
      Set.MapsTo (fun t => x + X.X t ω - rightLimit D t ω) s (Icc lo hi) →
      BoundedVariationOn
        (fun t => d t * w (x + X.X t ω - rightLimit D t ω)) s := by sorry
