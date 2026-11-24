-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_keyS_sR
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.keyS_sR
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:15.672703+00:00
-- url     : https://prove2.me/theorems/4ee27fea-d315-46b1-a9ed-f32a42ac1713
-- title:
--   Sign Antidiagonal: key S s R
-- statement:
--   The Sign Antidiagonal construction uses the key S s R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondExpansionIdentity.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondExpansionIdentity.lean#L16-L19

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.keyS_sR (k r m : ℕ) (hm : m ≤ r) (l : Fin m) : keyS k r (sR k r m hm l) = l.val := by sorry
