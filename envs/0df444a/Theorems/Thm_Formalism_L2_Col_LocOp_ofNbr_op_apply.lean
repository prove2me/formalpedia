-- Prove2me | Theorems.Thm_Formalism_L2_Col_LocOp_ofNbr_op_apply
-- name    : Formalism.L2.Col.LocOp.ofNbr_op_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:52:07.854817+00:00
-- url     : https://prove2.me/theorems/d2facb03-153b-420d-ac42-9a4887ce3c67
-- title:
--   Loc Op: of Nbr op apply
-- statement:
--   The Loc Op construction uses the of Nbr op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L351-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L351-L357

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

theorem Formalism.L2.Col.LocOp.ofNbr_op_apply (tr : S'.G →* S.G) (nb : S'.D → Finset S.D) (T : S.V →ₗ[K] S'.V)
    (hn : ∀ g d' d, tr g • d ∈ nb (g • d') ↔ d ∈ nb d') (hT : ∀ g x, T (S.ρ (tr g) x) = S'.ρ g (T x))
    (φ : S.EqFun) (d' : S'.D) :
    (((ofNbr tr nb T hn hT).op φ : S'.EqFun) : S'.D → S'.V) d' = ∑ d ∈ nb d', T ((φ : S.D → S.V) d) := by sorry
