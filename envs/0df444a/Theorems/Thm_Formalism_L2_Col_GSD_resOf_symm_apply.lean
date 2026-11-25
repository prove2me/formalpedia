-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_resOf_symm_apply
-- name    : Formalism.L2.Col.GSD.resOf_symm_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:43:47.631373+00:00
-- url     : https://prove2.me/theorems/9be6f98e-39bb-4f68-9502-1a70329c9ab1
-- title:
--   GSD: res Of symm apply
-- statement:
--   The GSD construction uses the res Of symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L198-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L198-L199

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

theorem Formalism.L2.Col.GSD.resOf_symm_apply (h : S.Ok) (s : S.Sec) (f : (S.toCSDOf h s).Forms) (d : S.D) :
    (((S.resOf h s).symm f : S.EqFun) : S.D → S.V) d = S.ρ (s.mv d) ((f.1 : S.Cl → S.V) (S.cls d)) := by sorry
