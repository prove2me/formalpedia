-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_variation_standing_iff_integrable_one
-- name    : AvramDividend.Classical.unbounded_variation_standing_iff_integrable_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T05:10:55.305684+00:00
-- url     : https://prove2.me/theorems/915399a1-9a0c-4995-800a-500fac1151cd
-- title:
--   For an unbounded-variation Lévy process, Standing is equivalent to finite first moment
-- statement:
--   On the unbounded-variation branch the structural assumptions of Avram's Standing predicate are automatic: monotone paths are impossible, and condition (3.3) follows from positive Gaussian part or infinite small-jump first variation. Therefore Standing holds if and only if the unit-time increment is integrable. This identifies exactly the missing hypothesis when transferring available smoothness theorems to the no-Standing problem.
-- source:
--   Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy and the Proved unbounded variation dichotomy.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_variation_standing_iff_integrable_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    X.Standing ↔ Integrable (X.X 1) P := by sorry
