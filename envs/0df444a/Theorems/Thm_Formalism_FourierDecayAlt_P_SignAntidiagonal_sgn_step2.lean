-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sgn_step2
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.sgn_step2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:22:51.169468+00:00
-- url     : https://prove2.me/theorems/4236c787-0f1d-4ed4-b557-f53765b8a748
-- title:
--   Sign Antidiagonal: sgn step2
-- statement:
--   The Sign Antidiagonal construction uses the sgn step2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SignPermutationIdentity.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SignPermutationIdentity.lean#L21-L31

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.sgn_step2 (s : ℕ) : s * (s - 1) / 2 + (s + 2) * (s + 2 - 1) / 2 = s * (s + 1) + 1 := by sorry
