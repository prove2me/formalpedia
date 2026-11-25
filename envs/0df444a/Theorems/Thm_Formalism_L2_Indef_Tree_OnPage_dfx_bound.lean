-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_dfx_bound
-- name    : Formalism.L2.Indef.Tree.OnPage.dfx_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:33:03.880802+00:00
-- url     : https://prove2.me/theorems/9a3c6a99-b90a-54a4-bc27-036fc6702a36
-- title:
--   On Page: dfx bound
-- statement:
--   The On Page construction uses the dfx bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L278-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L278-L309

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

theorem Formalism.L2.Indef.Tree.OnPage.dfx_bound (DF x k f m b T de2 PP D C2 : ℝ) (hDF0 : 0 ≤ DF) (hPP : 1 ≤ PP) (hD : 1 ≤ D)
    (hT : PP ^ 4 * D ^ 3 * k * f * x ≤ T * m * de2) (hde0 : 0 ≤ de2) (hde1 : de2 ≤ 1)
    (hZ3 : T * DF ≤ 3 * C2 * k * f * b) (hC2 : 0 ≤ C2) (hk : 0 < k) (hf : 0 < f) (hx0 : 0 ≤ x)
    (hm0 : 0 ≤ m) (hb0 : 0 ≤ b) : DF * x ≤ 3 * C2 * m * b := by sorry
