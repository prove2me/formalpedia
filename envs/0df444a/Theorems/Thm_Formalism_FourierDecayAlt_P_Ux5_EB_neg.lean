-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_neg
-- name    : Formalism.FourierDecayAlt.P.Ux5.EB_neg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:54:05.816617+00:00
-- url     : https://prove2.me/theorems/94855c0d-1e97-4d86-8ca4-d79a2917a497
-- title:
--   Ux5: EB neg
-- statement:
--   The Ux5 construction uses the EB neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L36-L38

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

theorem Formalism.FourierDecayAlt.P.Ux5.EB_neg {m n : Type*} {A : Matrix m n ℂ} {a : ℝ} (h : EB A a) : EB (-A) a := by sorry
