-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_toCSDOf_rat
-- name    : Formalism.L2.Col.GSD.toCSDOf_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:58.960908+00:00
-- url     : https://prove2.me/theorems/8ea7d9fa-b414-4340-a14f-5e8603cafdb1
-- title:
--   GSD: to CSDOf rat
-- statement:
--   The GSD construction uses the to CSDOf rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L242-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L242-L245

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

theorem Formalism.L2.Col.GSD.toCSDOf_rat (h : S.Ok) (R : S.Rat) (s : S.Sec) : (S.toCSDOf h s).Rat := by sorry
