-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sgnW_succ
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.sgnW_succ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:22:59.222333+00:00
-- url     : https://prove2.me/theorems/27144c79-7f6e-4994-a901-7b585efe64ff
-- title:
--   Sign Antidiagonal: sgn W succ
-- statement:
--   The Sign Antidiagonal construction uses the sgn W succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SignPermutationIdentity.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SignPermutationIdentity.lean#L44-L50

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.sgnW_succ (m : ℕ) : sgnW (m + 1) = (-1) ^ m * sgnW m := by sorry
