-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_keyS_esI
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.keyS_esI
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:26:13.858068+00:00
-- url     : https://prove2.me/theorems/05c4bd21-0768-4ac0-aae1-234d05904175
-- title:
--   Sign Antidiagonal: key S es I
-- statement:
--   The Sign Antidiagonal construction uses the key S es I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstExpansionIdentity.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstExpansionIdentity.lean#L17-L21

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
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
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.keyS_esI (k r : ℕ) (x : Fin r) : keyS k r (esI k r x) = x.val := by sorry
