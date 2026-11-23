-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lowering_relation_diagonal_right
-- name    : Formalism.FourierDecayAlt.P.Mx6.lowering_relation_diagonal_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:16:57.841856+00:00
-- url     : https://prove2.me/theorems/3af0eaa6-322c-4d1b-a3f2-d95276ec516c
-- title:
--   Mx6: lowering relation diagonal right
-- statement:
--   The Mx6 construction uses the lowering relation diagonal right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1618-L1626
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1618-L1626

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

theorem Formalism.FourierDecayAlt.P.Mx6.lowering_relation_diagonal_right (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (dA P u * lA P v - lA P v * dA P u) = dA P u * (lA P u - lA P v) := by sorry
