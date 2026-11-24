-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_gN_le_of_EB
-- name    : Formalism.FourierDecayAlt.P.Ux5.gN_le_of_EB
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:54:43.324923+00:00
-- url     : https://prove2.me/theorems/f50e6242-c7c8-488f-bb15-18deaea3e28b
-- title:
--   Ux5: g N le of EB
-- statement:
--   The Ux5 construction uses the g N le of EB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L626-L638
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L626-L638

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

theorem Formalism.FourierDecayAlt.P.Ux5.gN_le_of_EB {k r : ℕ} (M : B.Mat k r) {c : ℝ} (h : EB M c) (hc : 0 ≤ c) :
    B.gN M ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c := by sorry
