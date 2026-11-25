-- Prove2me | Theorems.Thm_Formalism_L2_Col_ClsKer_appOf_eq_csOf
-- name    : Formalism.L2.Col.ClsKer.appOf_eq_csOf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:06.598819+00:00
-- url     : https://prove2.me/theorems/d2b20ea9-f047-5d48-b337-4c48986b4b70
-- title:
--   Cls Ker: app Of eq cs Of
-- statement:
--   The Cls Ker construction uses the app Of eq cs Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1058-L1059
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1058-L1059

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

theorem Formalism.L2.Col.ClsKer.appOf_eq_csOf {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec) (φ : S.D → S.V) (d' : S'.D) :
    A.appOf h s φ d' = S.csOf h s fun d => A.k d d' (φ d) := by sorry
