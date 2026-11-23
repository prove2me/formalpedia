-- Prove2me | Theorems.Thm_Formalism_L2_Col_LocOp_op_apply
-- name    : Formalism.L2.Col.LocOp.op_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:23.475246+00:00
-- url     : https://prove2.me/theorems/aa3c5270-48bf-4d92-8731-88b1c940df4b
-- title:
--   Loc Op: op apply
-- statement:
--   The Loc Op construction uses the op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L304-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L304-L305

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
open Formalism.L2.Col.LocOp
variable {S S' : GSD K} (A : LocOp S S')

theorem Formalism.L2.Col.LocOp.op_apply (φ : S.EqFun) (d' : S'.D) :
    ((A.op φ : S'.EqFun) : S'.D → S'.V) d' = (A.ker d').sum fun d k => k ((φ : S.D → S.V) d) := by sorry
