-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xEx_poly
-- name    : Formalism.FourierDecayAlt.P.Mx7.xEx_poly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:42:26.86843+00:00
-- url     : https://prove2.me/theorems/b692c2a8-d2e0-4af3-ae84-e06a93b6fcbd
-- title:
--   Mx7: x Ex poly
-- statement:
--   The Mx7 construction uses the x Ex poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1420-L1422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1420-L1422

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
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial

theorem Formalism.FourierDecayAlt.P.Mx7.xEx_poly (P : Par) (ex : Finset ℕ) (π : Ty P) (Y : ℂ) :
    xEx P ex π Y = (∏ i ∈ Icc 1 (P.k - 1) \ ex, (X + C (rho P π i : ℂ))).eval Y := by sorry
