-- Prove2me | Theorems.Thm_Formalism_L2_Col_BiPair_formOf_apply
-- name    : Formalism.L2.Col.BiPair.formOf_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:42:45.317351+00:00
-- url     : https://prove2.me/theorems/8e1c3b67-adb0-40d5-9a73-b4397e9bac4d
-- title:
--   Bi Pair: form Of apply
-- statement:
--   The Bi Pair construction uses the form Of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1075-L1076
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1075-L1076

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

theorem Formalism.L2.Col.BiPair.formOf_apply (h' : S'.Ok) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    P.formOf h' s' φ ψ = P.sumOf h' s' φ ψ := by sorry
