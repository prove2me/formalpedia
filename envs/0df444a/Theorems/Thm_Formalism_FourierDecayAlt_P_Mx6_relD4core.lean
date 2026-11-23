-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_relD4core
-- name    : Formalism.FourierDecayAlt.P.Mx6.relD4core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:33:18.873474+00:00
-- url     : https://prove2.me/theorems/5677ce32-ecf8-47b4-9c09-689dc3becf3e
-- title:
--   Mx6: rel D4core
-- statement:
--   The Mx6 construction uses the rel D4core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1639-L1662
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1639-L1662

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

theorem Formalism.FourierDecayAlt.P.Mx6.relD4core (hN : SSNorm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) (hP : P.OK)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (mt P u * lA P v - lA P v * mt P u) = kap P (hh P v - hh P u) * (ggiA P * ggiA P) := by sorry
