-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_ipOf_eq_csOf
-- name    : Formalism.L2.Col.GSD.ipOf_eq_csOf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:08.366676+00:00
-- url     : https://prove2.me/theorems/81e9607f-8559-57a1-9e85-737ad41578d5
-- title:
--   GSD: ip Of eq cs Of
-- statement:
--   The GSD construction uses the ip Of eq cs Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1040-L1041
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1040-L1041

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

theorem Formalism.L2.Col.GSD.ipOf_eq_csOf (h : S.Ok) (s : S.Sec) (φ ψ : S.D → S.V) :
    S.ipOf h s φ ψ = S.csOf h s fun d => S.pair (φ d) (ψ d) := by sorry
