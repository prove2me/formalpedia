-- Prove2me | Theorems.Thm_Formalism_L2_Col_GFam_resOf_apply
-- name    : Formalism.L2.Col.GFam.resOf_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:29:26.211249+00:00
-- url     : https://prove2.me/theorems/d5c870fe-9608-4363-bb80-cb63819d356c
-- title:
--   GFam: res Of apply
-- statement:
--   The GFam construction uses the res Of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L671-L672
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L671-L672

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
attribute [instance] GFam.finβ GFam.decβ GFam.addV GFam.modV GFam.modOV GFam.towV GFam.finιV GFam.decιV GFam.grpG
  GFam.actD
open Formalism.L2.Col.GFam
variable (F : GFam K)

theorem Formalism.L2.Col.GFam.resOf_apply (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) (c : F.Cl) :
    (F.resOf h s φ).1 c = ((φ c.1 : (F.mem c.1).EqFun) : F.D c.1 → F.V) ((s c.1).rep c.2) := by sorry
