-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sgn_step
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.sgn_step
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:22:37.263866+00:00
-- url     : https://prove2.me/theorems/f894b14a-6f50-4f2f-af92-7b4683939937
-- title:
--   Sign Antidiagonal: sgn step
-- statement:
--   The Sign Antidiagonal construction uses the sgn step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SignPermutationIdentity.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SignPermutationIdentity.lean#L9-L19

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SignPermutationIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.sgn_step (s : ℕ) : s * (s - 1) / 2 + (s + 1) * (s + 1 - 1) / 2 = s * s := by sorry
