-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_cube_le_two_exp
-- name    : Formalism.L2.Indef.Tree.OnPage.cube_le_two_exp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:45:18.021838+00:00
-- url     : https://prove2.me/theorems/2c411ac0-12ca-4e3c-a505-0b5068549e23
-- title:
--   On Page: cube le two exp
-- statement:
--   The On Page construction uses the cube le two exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L119-L123

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}

theorem Formalism.L2.Indef.Tree.OnPage.cube_le_two_exp (y : ℝ) (hy : 0 ≤ y) : y ^ 3 ≤ 2 * Real.exp y := by sorry
