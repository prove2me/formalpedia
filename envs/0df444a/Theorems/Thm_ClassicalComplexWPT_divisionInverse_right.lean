-- Prove2me | Theorems.Thm_ClassicalComplexWPT_divisionInverse_right
-- name    : ClassicalComplexWPT.divisionInverse_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:02:05.708576+00:00
-- url     : https://prove2.me/theorems/6d23d3b9-8abb-5a9d-9ab6-d83ff4649bbc
-- title:
--   Classical Complex WPT: division Inverse right
-- statement:
--   The Classical Complex WPT construction uses the division Inverse right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L236-L244
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L236-L244

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

theorem ClassicalComplexWPT.divisionInverse_right (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (b : L1Coeff (A × ℕ)) :
    divisionInverse d p hp b +
        highShift d (convolution (divisionInverse d p hp b) p) = b := by sorry
