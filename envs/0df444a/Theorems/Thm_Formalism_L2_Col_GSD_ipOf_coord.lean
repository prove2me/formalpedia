-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_ipOf_coord
-- name    : Formalism.L2.Col.GSD.ipOf_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:45.90592+00:00
-- url     : https://prove2.me/theorems/6e5f8cdf-aad7-47ce-9912-0cd4a018937c
-- title:
--   GSD: ip Of coord
-- statement:
--   The GSD construction uses the ip Of coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L113-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L113-L123

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

theorem Formalism.L2.Col.GSD.ipOf_coord (h : S.Ok) (s : S.Sec) (φ ψ : S.EqFun) :
    S.ipOf h s φ ψ = hform (S.toCSDOf h s).H (S.coordOf h s φ) (S.coordOf h s ψ) := by sorry
