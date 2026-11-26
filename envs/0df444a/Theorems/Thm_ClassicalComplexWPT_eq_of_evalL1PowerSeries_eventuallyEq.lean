-- Prove2me | Theorems.Thm_ClassicalComplexWPT_eq_of_evalL1PowerSeries_eventuallyEq
-- name    : ClassicalComplexWPT.eq_of_evalL1PowerSeries_eventuallyEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:03.22678+00:00
-- url     : https://prove2.me/theorems/cc851a08-b3a0-5969-8e0b-d7c8a204ebf7
-- title:
--   Classical Complex WPT: eq of eval L1 Power Series eventually Eq
-- statement:
--   The analytic function on the unit disc represented by an `ℓ¹` sequence
--   determines every coefficient.  The hypothesis is stated as germ equality,
--   which is exactly what is available after shrinking the common analytic
--   neighborhood in preparation uniqueness.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L222-L255
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L222-L255

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_Basic
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.eq_of_evalL1PowerSeries_eventuallyEq (a b : L1Sequence)
    (h : (fun w ↦ evalL1PowerSeries a w) =ᶠ[nhds 0]
      (fun w ↦ evalL1PowerSeries b w)) : a = b := by sorry
