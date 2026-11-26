-- Prove2me | Theorems.Thm_ClassicalComplexWPT_preparationCoefficient_zero
-- name    : ClassicalComplexWPT.preparationCoefficient_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:51.286822+00:00
-- url     : https://prove2.me/theorems/c94c7c8f-b0e9-4fc8-98fa-b27fc0a33537
-- title:
--   Classical Complex WPT: preparation Coefficient zero
-- statement:
--   The Classical Complex WPT construction uses the preparation Coefficient zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L77-L82
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L77-L82

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

theorem ClassicalComplexWPT.preparationCoefficient_zero {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hrem : normalizedPreparationRemainder p r hr d 0 = 0)
    (i : Fin d) : preparationCoefficient p r hr d i 0 = 0 := by sorry
