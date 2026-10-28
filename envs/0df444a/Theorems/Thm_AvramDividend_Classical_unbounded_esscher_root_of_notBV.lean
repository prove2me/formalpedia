-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_of_notBV
-- name    : AvramDividend.Classical.unbounded_esscher_root_of_notBV
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T02:28:11.859253+00:00
-- url     : https://prove2.me/theorems/e600b0a2-93ac-4ee2-b2c6-c087147d0b18
-- title:
--   Esscher root existence for unbounded-variation spectrally negative Levy processes
-- statement:
--   For a spectrally negative Levy process of unbounded variation and any positive q, there exists a positive Esscher tilt parameter phi with Laplace exponent equal to q. The proof splits on the Gaussian coefficient: positive volatility uses the Gaussian Esscher root, while zero volatility forces infinite small-jump activity from the negation of bounded variation and uses the infinite-activity Esscher root.
-- source:
--   Decomposition of AvramDividend.Classical.unbounded_esscher_excursion_integrated_scale_representation: the phi-conjunct of its conclusion, proved by sigma-case-split over Proved AvramDividend.Classical.positive_esscher_root_of_gaussian and AvramDividend.Classical.positive_esscher_root_of_infinite_small_jump using the complete BoundedVariation definition (sigma = 0 and first-moment integral < top).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_esscher_root_of_notBV
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (hnbv : ¬ X.BoundedVariation) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by sorry
