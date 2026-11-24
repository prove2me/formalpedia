-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_resOf_apply
-- name    : Formalism.L2.Col.GSD.resOf_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:28:54.145878+00:00
-- url     : https://prove2.me/theorems/ab82d2ca-b8e2-492c-8e0c-30944145b06e
-- title:
--   GSD: res Of apply
-- statement:
--   The GSD construction uses the res Of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L195-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L195-L196

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
attribute [instance] GSD.grpG GSD.actD GSD.addV GSD.modV GSD.modOV GSD.towV GSD.finιV GSD.decιV
open Formalism.L2.Col.GSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

theorem Formalism.L2.Col.GSD.resOf_apply (h : S.Ok) (s : S.Sec) (φ : S.EqFun) (c : S.Cl) :
    ((S.resOf h s φ).1 : S.Cl → S.V) c = (φ : S.D → S.V) (s.rep c) := by sorry
