-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_keyS_wI
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.keyS_wI
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:59:39.871079+00:00
-- url     : https://prove2.me/theorems/44c6cf62-959d-4d81-b6bf-2c11a852488b
-- title:
--   Sign Antidiagonal: key S w I
-- statement:
--   The Sign Antidiagonal construction uses the key S w I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourthExpansionIdentity.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourthExpansionIdentity.lean#L25-L27

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarInverseSimplification
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthExpansionIdentity
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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.keyS_wI (k r : ℕ) (w : Fin (k + 1)) : keyS k r (wI k r w) = r + w.val + r := by sorry
