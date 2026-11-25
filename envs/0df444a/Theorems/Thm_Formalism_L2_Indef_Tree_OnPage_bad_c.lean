-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_bad_c
-- name    : Formalism.L2.Indef.Tree.OnPage.bad_c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:44:16.51099+00:00
-- url     : https://prove2.me/theorems/b3723859-33a0-479b-aa6b-09cbbfd0aa08
-- title:
--   On Page: bad c
-- statement:
--   The On Page construction uses the bad c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L153-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L153-L174

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

theorem Formalism.L2.Indef.Tree.OnPage.bad_c (C m v w fSe T f b s L C2 : ℝ) (hC : 0 ≤ C) (hv0 : 0 ≤ v) (hs : 0 ≤ s) (hv1 : s * (2 + v) ≤ 11 * L)
    (hw0 : 0 ≤ w + fSe) (hw : w ≤ 2 * f * b) (hfS : fSe ≤ f * b) (hT : T ≤ b) (hf : 8 ≤ f) (hm : 44 ≤ m) (hb : 1 ≤ b)
    (hC2 : 66 * C + 4 ≤ C2) :
    s * (2 * (C * m * (2 + v) * (w + fSe)) + 2 * T + 2) ≤ C2 * (f * m * b * L) := by sorry
