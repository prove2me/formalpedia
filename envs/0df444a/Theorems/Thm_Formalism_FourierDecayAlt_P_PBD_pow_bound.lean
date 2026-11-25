-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_pow_bound
-- name    : Formalism.FourierDecayAlt.P.PBD.pow_bound
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:10:05.811024+00:00
-- url     : https://prove2.me/theorems/00677f54-966e-4253-b9bf-40ef322574f7
-- title:
--   PBD: pow bound
-- statement:
--   The PBD construction uses the pow bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameThresholdBoundHolds.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameThresholdBoundHolds.lean#L22-L28

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameThresholdBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt

theorem Formalism.FourierDecayAlt.P.PBD.pow_bound (C x : ℝ) (n : ℕ) (hx : 0 ≤ x) (hC : 28 * Real.exp 1 ≤ C) :
    Real.exp 1 * (28 * x) ^ n ≤ C * (C * x) ^ n := by sorry
