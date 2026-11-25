-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_bad_d
-- name    : Formalism.L2.Indef.Tree.OnPage.bad_d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:33:00.579026+00:00
-- url     : https://prove2.me/theorems/10613628-8ad8-5b70-8d12-1d9e42e9c407
-- title:
--   On Page: bad d
-- statement:
--   The On Page construction uses the bad d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L176-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L176-L224

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

theorem Formalism.L2.Indef.Tree.OnPage.bad_d (T f r L b lg : ℝ) (hT0 : 0 ≤ T) (hT2 : T ^ 2 ≤ b) (hf : 8 ≤ f) (hr : 9 ≤ r) (hL : 10 ≤ L)
    (hZ : (f * r * L) ^ 12 ≤ b) (hlg0 : 0 ≤ lg) (hlg1 : lg ≤ 18 * L) : (4 * T + 4 * f * r ^ 2) * lg ≤ 4 * b := by sorry
