-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_abs_Ncz
-- name    : Formalism.FourierDecayAlt.P.Mx6.abs_Ncz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:28.892129+00:00
-- url     : https://prove2.me/theorems/38addcdc-7f6f-47ad-aa82-ad22a809f013
-- title:
--   Mx6: abs Ncz
-- statement:
--   The Mx6 construction uses the abs Ncz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1439-L1444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1439-L1444

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

theorem Formalism.FourierDecayAlt.P.Mx6.abs_Ncz (N g G z w : B) (t : ℂ) (hg : g = z * w - algebraMap ℂ B t) (hgG : g * G = 1)
    (hNz : N * z = z * N + 1) (hNG : N * G = G * N - w * G * G) :
    N * (z * G) = (z * G) * N - t • (G * G) := by sorry
