-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
-- name    : ClassicalComplexWPT.seqDivisionPerturbationMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:38.77495+00:00
-- url     : https://prove2.me/theorems/90042f27-938a-5aff-9b89-3ad58563bb16
-- title:
--   Classical Complex WPT: seq Division Perturbation Map apply
-- statement:
--   The Classical Complex WPT construction uses the seq Division Perturbation Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L590-L591
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L590-L591

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqDivisionPerturbationMap_apply (d : ℕ) (p : L1Coeff ℕ) :
    seqDivisionPerturbationMap d p = seqDivisionPerturbation d p := by sorry

attribute [defeq] ClassicalComplexWPT.seqDivisionPerturbationMap_apply
