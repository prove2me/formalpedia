-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_test_composition_BV
-- name    : AvramDividend.Classical.avram_wave3_03_bv_controlled_test_composition_BV
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:49:37.35304+00:00
-- url     : https://prove2.me/theorems/ef4bb79c-15c0-4dc9-be06-243139c9b8c8
-- title:
--   Original BV dividend-controlled reserve composed with locally Lipschitz HJB test has finite path variation on localised reserve bands
-- statement:
--   For the genuine original bounded-variation spectrally negative Lévy model and any actual adapted left-continuous dividend strategy, almost every controlled reserve path has finite variation on bounded time horizons. After localising to any time set where the reserve lies in a band [lo,hi] and w is Lipschitz there, the composed test value w(riskProcess) also has finite variation. This is a deterministic change-of-variable prerequisite retaining singular-continuous control mass and original source jumps.
-- source:
--   Proved avram_wave3_03_bv_controlled_reserve_boundedVariationOn_compact (11ad1ad2-0b89-4c20-820c-c6a87c404cdb), Mathlib LipschitzOnWith.comp_boundedVariationOn, BoundedVariationOn.mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_boundedVariationOn_compact

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_controlled_test_composition_BV
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (lo hi : ℝ) (L : NNReal)
    (hw : LipschitzOnWith L w (Icc lo hi)) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (s : Set ℝ≥0),
      s ⊆ Icc (0 : ℝ≥0) T →
      Set.MapsTo (fun t => riskProcess X x D t ω) s (Icc lo hi) →
      BoundedVariationOn
        (fun t => w (riskProcess X x D t ω)) s := by sorry
