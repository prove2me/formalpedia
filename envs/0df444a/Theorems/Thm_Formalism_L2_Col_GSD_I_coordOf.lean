-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_I_coordOf
-- name    : Formalism.L2.Col.GSD.I_coordOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:03.612376+00:00
-- url     : https://prove2.me/theorems/bbf9a31a-4d70-42c7-b0c2-e0c9f224a307
-- title:
--   GSD: I coord Of
-- statement:
--   The GSD construction uses the I coord Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L66-L71

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
open Formalism.L2.Col.GSD
variable (S : GSD K)

theorem Formalism.L2.Col.GSD.I_coordOf (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    (S.toCSDOf h s).I (S.coordOf h s φ) = fun c => (φ : S.D → S.V) (s.rep c) := by sorry
