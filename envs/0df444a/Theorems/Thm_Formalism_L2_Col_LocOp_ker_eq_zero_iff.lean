-- Prove2me | Theorems.Thm_Formalism_L2_Col_LocOp_ker_eq_zero_iff
-- name    : Formalism.L2.Col.LocOp.ker_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:16.056868+00:00
-- url     : https://prove2.me/theorems/d2effcc6-2c9e-42b7-97d8-4ad2e724f7d9
-- title:
--   Loc Op: ker eq zero iff
-- statement:
--   The Loc Op construction uses the ker eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L510-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L510-L524

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

theorem Formalism.L2.Col.LocOp.ker_eq_zero_iff (A : LocOp S S') (B : LocOp S' S) (hn : S.pair.Nondegenerate)
    (hn' : S'.pair.Nondegenerate)
    (hadj : ∀ d d' x y, S'.pair (A.ker d' d x) y = S.pair x (B.ker d d' y)) (d : S.D) (d' : S'.D) :
    A.ker d' d = 0 ↔ B.ker d d' = 0 := by sorry
