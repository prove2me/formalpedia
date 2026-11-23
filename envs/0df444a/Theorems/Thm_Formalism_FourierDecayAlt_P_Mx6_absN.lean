-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_absN
-- name    : Formalism.FourierDecayAlt.P.Mx6.absN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:05.254305+00:00
-- url     : https://prove2.me/theorems/53d5afe0-dd94-41be-9cff-d60a853a27fb
-- title:
--   Mx6: abs N
-- statement:
--   The Mx6 construction uses the abs N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1585-L1588
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1585-L1588

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

theorem Formalism.FourierDecayAlt.P.Mx6.absN (g G X m0 l0 S12 L : B) (hXm : X * m0 = m0 * X) (hXG : X * G = G * X) (hSG : S12 * G = G * S12) :
    (g * X * m0 + S12) * (l0 + G * L) = g * X * m0 * l0 + g * m0 * G * (X * L) + S12 * l0 + G * (S12 * L) := by sorry
