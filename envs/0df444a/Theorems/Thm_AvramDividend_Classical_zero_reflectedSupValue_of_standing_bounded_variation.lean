-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_standing_bounded_variation
-- name    : AvramDividend.Classical.zero_reflectedSupValue_of_standing_bounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:55:46.712354+00:00
-- url     : https://prove2.me/theorems/7daa759d-4890-41e5-a36a-d7fd7ba44d6e
-- title:
--   Zero reflected-barrier valuation in the bounded-variation Lévy branch
-- statement:
--   For a bounded-variation spectrally negative Lévy process satisfying Standing, the expected discounted dividends from reflection at zero until ruin equal the q-scale derivative boundary value. In the finite negative-jump regime the payout is determined by positive drift until the first ruin-inducing jump, and the same first-jump compensation determines the right scale derivative. Infinite-activity cases require the corresponding limiting argument.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3, barrier valuation at c=0, bounded-variation branch; local dossier zero-barrier-focused-2026-10-25.md. This theorem is the separate BV prerequisite for the zero_reflectedSupValue_eq_barrierValue root-connected target.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_reflectedSupValue_of_standing_bounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry
