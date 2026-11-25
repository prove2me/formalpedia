-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_det_norm_le
-- name    : Formalism.FourierDecayAlt.P.Ux5.det_norm_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:10:06.847885+00:00
-- url     : https://prove2.me/theorems/489c14c6-b75e-48cb-b88a-fd45c570533c
-- title:
--   Ux5: det norm le
-- statement:
--   The Ux5 construction uses the det norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L75-L77

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5

theorem Formalism.FourierDecayAlt.P.Ux5.det_norm_le {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) {m : ℝ} (h : EB A m) :
    ‖A.det‖ ≤ (Fintype.card n).factorial * m ^ Fintype.card n := by sorry
