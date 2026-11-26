-- Prove2me | Theorems.Thm_ClassicalComplexWPT_lowShift_apply_of_lt
-- name    : ClassicalComplexWPT.lowShift_apply_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:02:13.702127+00:00
-- url     : https://prove2.me/theorems/e00fb811-5576-4731-aa1c-abe143cecd14
-- title:
--   Classical Complex WPT: low Shift apply of lt
-- statement:
--   The Classical Complex WPT construction uses the low Shift apply of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L89-L95
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L89-L95

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*}

theorem ClassicalComplexWPT.lowShift_apply_of_lt (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ}
    (hn : n < d) : lowShift d f (a,n) = 0 := by sorry
