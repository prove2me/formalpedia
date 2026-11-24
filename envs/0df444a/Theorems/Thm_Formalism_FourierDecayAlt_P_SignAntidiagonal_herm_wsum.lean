-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_herm_wsum
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_wsum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:34:23.834916+00:00
-- url     : https://prove2.me/theorems/ff6d748f-d6d1-4b01-83fe-953e8539b948
-- title:
--   Sign Antidiagonal: herm wsum
-- statement:
--   The Sign Antidiagonal construction uses the herm wsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThirdPeelingMinorMemIdeal.lean#L13-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThirdPeelingMinorMemIdeal.lean#L13-L43

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_wsum (k r : ℕ) (v y : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) :
    herm (Hpk k r) v y = ∑ w : Fin (k + 1), v (wI k r w) * herm (Hpk k r) (bvec (wI k r w)) y := by sorry
