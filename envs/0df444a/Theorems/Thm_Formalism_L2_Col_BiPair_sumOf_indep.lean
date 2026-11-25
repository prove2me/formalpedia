-- Prove2me | Theorems.Thm_Formalism_L2_Col_BiPair_sumOf_indep
-- name    : Formalism.L2.Col.BiPair.sumOf_indep
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:45:48.271717+00:00
-- url     : https://prove2.me/theorems/1a0258a8-bc1c-5384-b514-063e00fa67e0
-- title:
--   Bi Pair: sum Of indep
-- statement:
--   The Bi Pair construction uses the sum Of indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1070-L1073
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1070-L1073

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
open Formalism.L2.Col.BiPair
variable {S S' : GSD K} (P : BiPair S S')

theorem Formalism.L2.Col.BiPair.sumOf_indep (h' : S'.Ok) (s s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    P.sumOf h' s φ ψ = P.sumOf h' s' φ ψ := by sorry
