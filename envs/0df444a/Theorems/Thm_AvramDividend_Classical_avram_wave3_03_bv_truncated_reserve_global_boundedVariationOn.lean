-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_truncated_reserve_global_boundedVariationOn
-- name    : AvramDividend.Classical.avram_wave3_03_bv_truncated_reserve_global_boundedVariationOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:21:30.995194+00:00
-- url     : https://prove2.me/theorems/dfae1b88-e487-4124-80e7-143e9c94d482
-- title:
--   Original BV controlled reserve frozen after any horizon has global bounded variation
-- statement:
--   For the actual bounded-variation Lévy process and any admissible strategy, almost surely and uniformly over every finite horizon T, the controlled reserve path made constant after T is a globally bounded-variation real function on all nonnegative time. This directly meets the global-BV premise of Mathlib vector-measure integration-by-parts and avoids assuming a potentially infinite lifetime variation.
-- source:
--   Use canonical Proved compact controlled-reserve BV theorem 11ad1ad2 and Mathlib eVariationOn.comp_le_of_monotoneOn for monotone truncation t↦min t T, mapping all times into [0,T]. The exact controlled reserve, including continuous Stieltjes dividend mass, is retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_boundedVariationOn_compact

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_truncated_reserve_global_boundedVariationOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      BoundedVariationOn
        (fun t : ℝ≥0 => riskProcess X x D (min t T) ω) Set.univ := by sorry
