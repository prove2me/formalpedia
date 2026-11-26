-- Prove2me | Theorems.Thm_ClassicalComplexWPT_divisionInverse_left
-- name    : ClassicalComplexWPT.divisionInverse_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:02:34.353249+00:00
-- url     : https://prove2.me/theorems/4ca28a98-3f14-47d2-b916-8e5a28e5d611
-- title:
--   Classical Complex WPT: division Inverse left
-- statement:
--   The Classical Complex WPT construction uses the division Inverse left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L246-L253
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L246-L253

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]

theorem ClassicalComplexWPT.divisionInverse_left (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (q : L1Coeff (A × ℕ)) :
    divisionInverse d p hp (q + highShift d (convolution q p)) = q := by sorry
