-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_lt
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_lt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:34:28.084262+00:00
-- url     : https://prove2.me/theorems/1c52e146-03bb-421f-9dfe-1871c1cbdc6a
-- title:
--   Sign Antidiagonal: pe lt
-- statement:
--   The Sign Antidiagonal construction uses the pe lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThirdPeelingMinorMemIdeal.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThirdPeelingMinorMemIdeal.lean#L9-L11

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_lt {k r p : ℕ} (h : p < 2 * r + k + 1) : (pe k r p).val = p := by sorry
