-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_t_MajIsProf
-- name    : Formalism.FourierDecayAlt.P.Jx1.t_MajIsProf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:24.401257+00:00
-- url     : https://prove2.me/theorems/e0b11eee-813f-43c0-82fb-90391bf9ba0f
-- title:
--   Jx1: t Maj Is Prof
-- statement:
--   The Jx1 construction uses the t Maj Is Prof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L327-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L327-L332

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1

theorem Formalism.FourierDecayAlt.P.Jx1.t_MajIsProf : MajIsProf := by sorry
