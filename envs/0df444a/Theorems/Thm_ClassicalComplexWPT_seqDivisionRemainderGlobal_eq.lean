-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivisionRemainderGlobal_eq
-- name    : ClassicalComplexWPT.seqDivisionRemainderGlobal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:54.474902+00:00
-- url     : https://prove2.me/theorems/f0cd7e5e-afe4-57d5-93c0-0bb380d6f490
-- title:
--   Classical Complex WPT: seq Division Remainder Global eq
-- statement:
--   The Classical Complex WPT construction uses the seq Division Remainder Global eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L676-L679
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L676-L679

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqDivisionRemainderGlobal_eq (d : ℕ) (p f : L1Coeff ℕ) (hp : ‖p‖ < 1) :
    seqDivisionRemainderGlobal d (p,f) = seqDivisionRemainder d p hp f := by sorry
