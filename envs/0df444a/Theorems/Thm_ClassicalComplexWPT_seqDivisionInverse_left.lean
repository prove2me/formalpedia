-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivisionInverse_left
-- name    : ClassicalComplexWPT.seqDivisionInverse_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:06.430939+00:00
-- url     : https://prove2.me/theorems/5b546fcb-212c-4736-a00c-8769557c0929
-- title:
--   Classical Complex WPT: seq Division Inverse left
-- statement:
--   The Classical Complex WPT construction uses the seq Division Inverse left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L614-L622
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L614-L622

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqDivisionInverse_left (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (q : L1Coeff ℕ) :
    seqDivisionInverse d p hp (q + seqHighShift d (convolution q p)) = q := by sorry
