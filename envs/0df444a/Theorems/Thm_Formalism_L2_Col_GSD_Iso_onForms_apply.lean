-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_Iso_onForms_apply
-- name    : Formalism.L2.Col.GSD.Iso.onForms_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:43:18.487614+00:00
-- url     : https://prove2.me/theorems/fb2f5f61-d6b3-5ec6-867f-43359d6b5481
-- title:
--   Iso: on Forms apply
-- statement:
--   The Iso construction uses the on Forms apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L450-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L450-L451

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD Formalism.L2.Col.GSD.Iso
variable {S S' : GSD K} (e : GSD.Iso S S')

theorem Formalism.L2.Col.GSD.Iso.onForms_apply (φ : S.EqFun) (d' : S'.D) :
    ((e.onForms φ : S'.EqFun) : S'.D → S'.V) d' = e.eV ((φ : S.D → S.V) (e.eD.symm d')) := by sorry
