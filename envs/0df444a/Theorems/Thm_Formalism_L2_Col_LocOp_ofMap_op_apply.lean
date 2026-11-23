-- Prove2me | Theorems.Thm_Formalism_L2_Col_LocOp_ofMap_op_apply
-- name    : Formalism.L2.Col.LocOp.ofMap_op_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:33.212002+00:00
-- url     : https://prove2.me/theorems/54251ad8-53b3-46de-99d3-031293c3e0b1
-- title:
--   Loc Op: of Map op apply
-- statement:
--   The Loc Op construction uses the of Map op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L324-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L324-L330

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

theorem Formalism.L2.Col.LocOp.ofMap_op_apply (tr : S'.G →* S.G) (p : S'.D → S.D) (T : S.V →ₗ[K] S'.V)
    (hp : ∀ g d', p (g • d') = tr g • p d') (hT : ∀ g x, T (S.ρ (tr g) x) = S'.ρ g (T x)) (φ : S.EqFun)
    (d' : S'.D) : (((ofMap tr p T hp hT).op φ : S'.EqFun) : S'.D → S'.V) d' = T ((φ : S.D → S.V) (p d')) := by sorry
