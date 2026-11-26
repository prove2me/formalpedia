-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivision_factorizations_unique
-- name    : ClassicalComplexWPT.seqDivision_factorizations_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:38.760858+00:00
-- url     : https://prove2.me/theorems/8d1bc80d-d7d0-4ed8-9c9c-d1deb4b3a26d
-- title:
--   Classical Complex WPT: seq Division factorizations unique
-- statement:
--   Any two quotient/remainder decompositions for the same small normalized
--   divisor agree.  This is the form of `seqDivision_existsUnique` used by germ
--   uniqueness.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L260-L278
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L260-L278

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

theorem ClassicalComplexWPT.seqDivision_factorizations_unique (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f q₁ r₁ q₂ r₂ : L1Coeff ℕ)
    (hfac₁ : f = seqLowShift d q₁ + convolution q₁ p + r₁)
    (hr₁ : seqHighShift d r₁ = 0)
    (hfac₂ : f = seqLowShift d q₂ + convolution q₂ p + r₂)
    (hr₂ : seqHighShift d r₂ = 0) :
    q₁ = q₂ ∧ r₁ = r₂ := by sorry
