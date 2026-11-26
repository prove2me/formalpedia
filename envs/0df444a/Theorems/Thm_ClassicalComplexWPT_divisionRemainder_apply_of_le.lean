-- Prove2me | Theorems.Thm_ClassicalComplexWPT_divisionRemainder_apply_of_le
-- name    : ClassicalComplexWPT.divisionRemainder_apply_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:04:54.414879+00:00
-- url     : https://prove2.me/theorems/d569df11-d0b0-448b-b301-bf46dea21ad5
-- title:
--   Classical Complex WPT: division Remainder apply of le
-- statement:
--   The Classical Complex WPT construction uses the division Remainder apply of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L401-L404
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L401-L404

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

theorem ClassicalComplexWPT.divisionRemainder_apply_of_le (d : ℕ) (p : L1Coeff (A × ℕ))
    (hp : ‖p‖ < 1) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ} (hn : d ≤ n) :
    divisionRemainder d p hp f (a,n) = 0 := by sorry
