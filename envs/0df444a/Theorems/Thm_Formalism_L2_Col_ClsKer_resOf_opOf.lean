-- Prove2me | Theorems.Thm_Formalism_L2_Col_ClsKer_resOf_opOf
-- name    : Formalism.L2.Col.ClsKer.resOf_opOf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:10.394704+00:00
-- url     : https://prove2.me/theorems/a03b0ae6-8145-5830-988c-2067476d9623
-- title:
--   Cls Ker: res Of op Of
-- statement:
--   The Cls Ker construction uses the res Of op Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L196-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L196-L198

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
open Formalism.L2.Col.ClsKer
variable {S S' : GSD K} (A : ClsKer S S')

theorem Formalism.L2.Col.ClsKer.resOf_opOf (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) :
    (S'.resOf h' s' (A.opOf h s φ)).1 = letI := h.fintypeCl
      Formalism.ThetaLiftIndependence.kerOpM (fun c => (((S.toCSDOf h s).wt c : K))⁻¹) (A.atReps s s') (S.resOf h s φ).1 := by sorry
