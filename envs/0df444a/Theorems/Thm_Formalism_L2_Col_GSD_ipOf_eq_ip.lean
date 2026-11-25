-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_ipOf_eq_ip
-- name    : Formalism.L2.Col.GSD.ipOf_eq_ip
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:43:08.61667+00:00
-- url     : https://prove2.me/theorems/57c3cecf-48f5-4e34-8ed2-3c67b6a992bd
-- title:
--   GSD: ip Of eq ip
-- statement:
--   The GSD construction uses the ip Of eq ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L144-L145

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

theorem Formalism.L2.Col.GSD.ipOf_eq_ip (h : S.Ok) (s : S.Sec) (φ ψ : S.EqFun) : S.ipOf h s φ ψ = S.ip h φ ψ := by sorry
