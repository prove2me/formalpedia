-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_majorant_is_profinite
-- name    : Formalism.FourierDecayAlt.P.majorant_is_profinite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:34:33.232158+00:00
-- url     : https://prove2.me/theorems/e8a3d505-7b4f-4c91-9076-ac3ffaea7ec5
-- title:
--   P: majorant is profinite
-- statement:
--   The P construction uses the majorant is profinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L479-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L479-L479

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.majorant_is_profinite : Formalism.FourierDecayAlt.J.MajIsProf := by sorry
