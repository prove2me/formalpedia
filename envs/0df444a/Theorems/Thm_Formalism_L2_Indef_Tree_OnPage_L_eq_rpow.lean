-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_L_eq_rpow
-- name    : Formalism.L2.Indef.Tree.OnPage.L_eq_rpow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:33:58.586821+00:00
-- url     : https://prove2.me/theorems/614f3557-1231-52e6-ace5-c066fb937321
-- title:
--   On Page: L eq rpow
-- statement:
--   The On Page construction uses the L eq rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L90-L92

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

theorem Formalism.L2.Indef.Tree.OnPage.L_eq_rpow (O : OnObj S P c) : O.L = O.x ^ O.eps := by sorry
