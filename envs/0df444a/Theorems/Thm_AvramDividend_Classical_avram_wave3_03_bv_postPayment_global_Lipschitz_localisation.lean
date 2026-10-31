-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_global_Lipschitz_localisation
-- name    : AvramDividend.Classical.avram_wave3_03_bv_postPayment_global_Lipschitz_localisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:43:47.59408+00:00
-- url     : https://prove2.me/theorems/d63acbe5-5c82-403f-98ee-f487045481f5
-- title:
--   Compact-band HJB test admits globally Lipschitz extension with BV post-payment path
-- statement:
--   Given an HJB value test locally Lipschitz on a compact surplus band, construct a genuine globally Lipschitz extension agreeing on that band. Along the original BV Levy source process with its actual post-payment right-dividend atoms, the extended test evaluated at every finite-horizon frozen reserve has globally bounded variation almost surely, uniformly in the horizon.
-- source:
--   Mathlib LipschitzOnWith.extend_real global extension and LipschitzWith.comp_boundedVariationOn applied to the Proved original post-payment globally clipped reserve (1035f03b-d6ec-49b6-8ca5-1a20fc8e71be). Supports Stieltjes vector-measure integration by parts after localisation, but does not itself discharge the Lévy generator compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_postPayment_global_Lipschitz_localisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (lo hi : ℝ) (L : NNReal)
    (hw : LipschitzOnWith L w (Icc lo hi)) :
    ∃ v : ℝ → ℝ,
      LipschitzWith L v ∧ Set.EqOn w v (Icc lo hi) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        BoundedVariationOn
          (fun t : ℝ≥0 => v
            (x + X.X (min t T) ω - rightLimit D (min t T) ω))
          Set.univ := by sorry
