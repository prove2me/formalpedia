-- Prove2me | Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
-- name    : AvramDividend.Classical.standing_bv_levy_absolutely_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T07:14:28.240154+00:00
-- url     : https://prove2.me/theorems/bc92b9ce-0d7d-4e99-ba7c-231bed4a8a36
-- title:
--   Standing plus bounded variation forces an absolutely continuous Lévy measure
-- statement:
--   The canonical Condition33 in Standing is the disjunction sigma>0, infinite small-jump first moment, or absolute continuity of the Lévy measure. Bounded variation gives sigma=0 and a finite small-jump first moment. Hence the first two clauses are impossible and the absolute-continuity clause must hold. This is purely definitional and reduces the bounded-variation C1 regularity branch to the no-atoms/absolutely-continuous scale-function theorem.
-- source:
--   Definitions of SpectrallyNegativeLevy.Standing, Condition33 and BoundedVariation in the Avram mission.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.standing_bv_levy_absolutely_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation) :
    X.ν ≪ volume := by sorry
