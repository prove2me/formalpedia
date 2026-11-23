-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_compC_diag
-- name    : Formalism.FourierDecayAlt.P.Mx7.compC_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:46.300914+00:00
-- url     : https://prove2.me/theorems/3c846ce0-b634-4f8f-8cdc-97712f323376
-- title:
--   Mx7: comp C diag
-- statement:
--   The Mx7 construction uses the comp C diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L235-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L235-L239

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

theorem Formalism.FourierDecayAlt.P.Mx7.compC_diag (hSh : SSShift) (hR : RhoUp) (P : Par) (u v : ℂ) (l : ℕ) :
    (SS P l * kap P fun π => xEx P {l} π u) * (SS P l * kap P fun π => xEx P {l} π v) =
      (SS P l * kap P fun π => xEx P {l} π v) * (SS P l * kap P fun π => xEx P {l} π u) := by sorry
