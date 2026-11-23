-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_abs_Nc
-- name    : Formalism.FourierDecayAlt.P.Mx6.abs_Nc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:17.106679+00:00
-- url     : https://prove2.me/theorems/835abc8f-512f-43be-b0b5-f23dce6df9ed
-- title:
--   Mx6: abs Nc
-- statement:
--   The Mx6 construction uses the abs Nc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1422-L1424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1422-L1424

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem Formalism.FourierDecayAlt.P.Mx6.abs_Nc (N w G : B) (hNw : N * w = w * N) (hNG : N * G = G * N - w * G * G) (hGw : G * w = w * G) :
    N * (w * G) = (w * G) * N - (w * G) * (w * G) := by sorry
