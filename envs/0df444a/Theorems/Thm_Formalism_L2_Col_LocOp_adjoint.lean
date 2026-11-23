-- Prove2me | Theorems.Thm_Formalism_L2_Col_LocOp_adjoint
-- name    : Formalism.L2.Col.LocOp.adjoint
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:16.689961+00:00
-- url     : https://prove2.me/theorems/232bc8a0-82a1-4932-9e06-f092659aa281
-- title:
--   Loc Op: adjoint
-- statement:
--   The Loc Op construction uses the adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L526-L596
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L526-L596

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.LocOp
variable {S S' : GSD K}

theorem Formalism.L2.Col.LocOp.adjoint (A : LocOp S S') (B : LocOp S' S) (h : S.Ok) (h' : S'.Ok) (e : S.G ≃* S'.G)
    (hB : ∀ g, B.tr g = e g)
    (hsupp : ∀ d d', A.ker d' d = 0 ↔ B.ker d d' = 0)
    (hadj : ∀ d d' x y, S'.pair (A.ker d' d x) y = S.pair x (B.ker d d' y))
    (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    S'.ipOf h' s' (A.app φ) ψ = S.ipOf h s φ (B.app ψ) := by sorry
