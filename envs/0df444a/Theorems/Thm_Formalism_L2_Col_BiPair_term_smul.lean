-- Prove2me | Theorems.Thm_Formalism_L2_Col_BiPair_term_smul
-- name    : Formalism.L2.Col.BiPair.term_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:42.52286+00:00
-- url     : https://prove2.me/theorems/c7017504-f89f-4039-99ca-1165970f6bca
-- title:
--   Bi Pair: term smul
-- statement:
--   The Bi Pair construction uses the term smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1065-L1068
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1065-L1068

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

theorem Formalism.L2.Col.BiPair.term_smul (φ : S.EqFun) (ψ : S'.EqFun) (g : S'.G) (d' : S'.D) :
    P.B ((φ : S.D → S.V) (P.p (g • d'))) ((ψ : S'.D → S'.V) (g • d')) =
      P.B ((φ : S.D → S.V) (P.p d')) ((ψ : S'.D → S'.V) d') := by sorry
