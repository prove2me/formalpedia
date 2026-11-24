-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_scal_E
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.scal_E
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:52:07.68991+00:00
-- url     : https://prove2.me/theorems/a9e89cbd-788d-497c-beda-ba570debaa18
-- title:
--   Sign Antidiagonal: scal E
-- statement:
--   The Sign Antidiagonal construction uses the scal E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L74-L80

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr
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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.scal_E (dh t σ ε : ℂ) (s' : ℕ) (hdh : dh ≠ 0) (ht : t ≠ 0) (hσ : σ * σ = 1) (hε : ε * ε = 1) :
    (dh * t ^ (s' + 1) * (ε * σ))⁻¹ * (dh * t ^ s' * σ) = ε * t⁻¹ * (dh⁻¹ * dh) := by sorry
