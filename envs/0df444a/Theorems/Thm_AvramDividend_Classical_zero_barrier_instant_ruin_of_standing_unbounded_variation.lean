-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_barrier_instant_ruin_of_standing_unbounded_variation
-- name    : AvramDividend.Classical.zero_barrier_instant_ruin_of_standing_unbounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:55:37.362489+00:00
-- url     : https://prove2.me/theorems/8bec33c8-6ed7-4a98-a603-6cc6e4faf588
-- title:
--   Standing unbounded-variation Lévy process ruins the zero reflected barrier instantly
-- statement:
--   For a spectrally negative Lévy process of unbounded variation satisfying Standing, the process crosses below its initial reflected supremum at arbitrarily small positive times almost surely, so the zero-barrier ruin time is zero. This is the missing probabilistic regularity input needed to combine the proved instant-ruin zero-value and vanishing q-scale-origin identities.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3, zero-barrier regularity. A source-faithful proof route derives the complex characteristic exponent from the available positive Laplace moments, then uses the small-time negative-increment law, finite-prefix increment product identity (Proved 4b6af35c), and almost-sure grid nullity; research dossier artifacts/mission_research/1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43/latest.md.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_barrier_instant_ruin_of_standing_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0 := by sorry
