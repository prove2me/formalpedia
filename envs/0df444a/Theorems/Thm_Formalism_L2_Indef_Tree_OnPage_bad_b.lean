-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_bad_b
-- name    : Formalism.L2.Indef.Tree.OnPage.bad_b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:07.726584+00:00
-- url     : https://prove2.me/theorems/bf695d96-0c3b-5349-8c83-b75cffc35d44
-- title:
--   On Page: bad b
-- statement:
--   The On Page construction uses the bad b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L131-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L131-L151

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

theorem Formalism.L2.Indef.Tree.OnPage.bad_b (w fSe T fkb lq f m b C1 : ℝ) (hw : w ≤ 2 * f * b) (hfS : fSe ≤ f * b) (hT : T ≤ b)
    (hfk : fkb ≤ f * b) (hlq0 : 0 ≤ lq) (hlq : lq ≤ m) (hf : 8 ≤ f) (hm : 44 ≤ m) (hb : 1 ≤ b)
    (hC1 : 14 ≤ C1) : (2 * (w + fSe + T + 1) + 4 * fkb) * lq ≤ C1 * (f * m * b) := by sorry
