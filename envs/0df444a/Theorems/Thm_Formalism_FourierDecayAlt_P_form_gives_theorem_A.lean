-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_form_gives_theorem_A
-- name    : Formalism.FourierDecayAlt.P.form_gives_theorem_A
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:31:48.831009+00:00
-- url     : https://prove2.me/theorems/6960b453-ccf3-56f5-bd46-ae39904d16a6
-- title:
--   P: form gives theorem A
-- statement:
--   The P construction uses the form gives theorem A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L184-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L184-L207

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx6

theorem Formalism.FourierDecayAlt.P.form_gives_theorem_A : Formalism.FourierDecayAlt.J.FormGivesMain := by sorry
