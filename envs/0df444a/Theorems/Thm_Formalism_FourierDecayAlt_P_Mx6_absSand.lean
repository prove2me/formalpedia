-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_absSand
-- name    : Formalism.FourierDecayAlt.P.Mx6.absSand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:16.102511+00:00
-- url     : https://prove2.me/theorems/9f334e3f-1b52-49a3-832f-981f9ee081b6
-- title:
--   Mx6: abs Sand
-- statement:
--   The Mx6 construction uses the abs Sand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1580-L1583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1580-L1583

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

theorem Formalism.FourierDecayAlt.P.Mx6.absSand (g G K1 K2 K3 : B) (hgG : g * G = 1) (hGg : G * g = 1)
    (h1 : K1 * G = G * K1) (h2 : K2 * G = G * K2) (h1g : K1 * g = g * K1) (h2g : K2 * g = g * K2) :
    g * K1 * (K2 * (G * G)) * (g * K3) = K1 * K2 * K3 := by sorry
