-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_ti_mul
-- name    : Formalism.FourierDecayAlt.P.Mx7.ti_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:42.911827+00:00
-- url     : https://prove2.me/theorems/0c451981-daf1-4995-be65-8fb050af1b22
-- title:
--   Mx7: ti mul
-- statement:
--   The Mx7 construction uses the ti mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1205-L1209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1205-L1209

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

theorem Formalism.FourierDecayAlt.P.Mx7.ti_mul (P : Par) (a b : ℂ) :
    ti P a * ti P b = ggiA P * ggiA P * kap P fun π => (xC P π a)⁻¹ * (xC P π b)⁻¹ := by sorry
