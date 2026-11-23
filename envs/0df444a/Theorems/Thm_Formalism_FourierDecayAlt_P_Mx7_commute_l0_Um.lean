-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_commute_l0_Um
-- name    : Formalism.FourierDecayAlt.P.Mx7.commute_l0_Um
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:16.492472+00:00
-- url     : https://prove2.me/theorems/8c5a8af6-b8e6-45e3-b1ee-cae5535b440d
-- title:
--   Mx7: commute l0 Um
-- statement:
--   The Mx7 construction uses the commute l0 Um property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1290-L1303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1290-L1303

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

theorem Formalism.FourierDecayAlt.P.Mx7.commute_l0_Um (hSc : SSScalar) (hN : NabSS) (hSG : StarGens) (hLN : LevNab) (P : Par) (u : ℂ) :
    Commute (l0A P u) (ggiA P * Um P u) := by sorry
