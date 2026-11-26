-- Prove2me | Theorems.Thm_ClassicalComplexWPT_preparedPolynomial_preparationCoefficient
-- name    : ClassicalComplexWPT.preparedPolynomial_preparationCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:07.32285+00:00
-- url     : https://prove2.me/theorems/32c77b33-0cf2-53c0-b8ec-8420517b5586
-- title:
--   Classical Complex WPT: prepared Polynomial preparation Coefficient
-- statement:
--   The Classical Complex WPT construction uses the prepared Polynomial preparation Coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L84-L114
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L84-L114

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence
set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.preparedPolynomial_preparationCoefficient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) (hr0 : 0 < r)
    (z : Base n) (w : ℂ) :
    preparedPolynomial d (preparationCoefficient p r hr d) (z, w) =
      (r : ℂ) ^ d *
        ((r : ℂ)⁻¹ ^ d * w ^ d -
          ∑ i : Fin d, normalizedPreparationRemainder p r hr d z i *
            ((r : ℂ)⁻¹ * w) ^ (i : ℕ)) := by sorry
