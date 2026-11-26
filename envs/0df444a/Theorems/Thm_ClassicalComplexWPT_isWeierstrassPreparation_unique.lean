-- Prove2me | Theorems.Thm_ClassicalComplexWPT_isWeierstrassPreparation_unique
-- name    : ClassicalComplexWPT.isWeierstrassPreparation_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:44.862118+00:00
-- url     : https://prove2.me/theorems/314152d2-fcdb-4649-b0f6-2c3c4d759bbb
-- title:
--   Classical Complex WPT: is Weierstrass Preparation unique
-- statement:
--   Full germ uniqueness of Weierstrass preparation witnesses.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L351-L459
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L351-L459

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

theorem ClassicalComplexWPT.isWeierstrassPreparation_unique {n d : ℕ} {f : Ambient n → ℂ}
    {a a' : Fin d → Base n → ℂ} {u u' : Ambient n → ℂ}
    (h : IsWeierstrassPreparation f d a u)
    (h' : IsWeierstrassPreparation f d a' u') :
    (∀ i, a i =ᶠ[nhds 0] a' i) ∧ u =ᶠ[nhds 0] u' := by sorry
