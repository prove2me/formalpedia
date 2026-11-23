-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_generic
-- name    : Formalism.FourierDecayAlt.P.Mx6.generic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:12:28.059617+00:00
-- url     : https://prove2.me/theorems/aa276bb8-35f4-4c4e-9df5-48f3b2ba954b
-- title:
--   Mx6: generic
-- statement:
--   The Mx6 construction uses the generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1809-L1842
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1809-L1842

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
noncomputable section
variable (P : Par)

theorem Formalism.FourierDecayAlt.P.Mx6.generic (hN : SSNorm) (hC : SSComm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) (hP : P.OK)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) (h0 : u - v ≠ 0) (h1 : u - v ≠ 1) (h2 : u - v ≠ -1)
    (i j k l : Fin 2) :
    (u - v) • (QQr P u i j * QQr P v k l - QQr P v k l * QQr P u i j) =
      QQr P u k j * QQr P v i l - QQr P v k j * QQr P u i l := by sorry
