-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_mul_w_w
-- name    : Formalism.FourierDecayAlt.P.Ux5.mul_w_w
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:29:09.063663+00:00
-- url     : https://prove2.me/theorems/763b2cf9-c603-4142-b5bb-f4e9cf263dac
-- title:
--   Ux5: mul w w
-- statement:
--   The Ux5 construction uses the mul w w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L663-L664
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L663-L664

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

theorem Formalism.FourierDecayAlt.P.Ux5.mul_w_w {j : ℕ} {ι : Type*} (M : Matrix (Fin j) ι ℂ) : G.wMat j * (G.wMat j * M) = M := by sorry
