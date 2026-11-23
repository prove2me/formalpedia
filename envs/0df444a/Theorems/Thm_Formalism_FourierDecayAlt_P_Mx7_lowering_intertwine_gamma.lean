-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_lowering_intertwine_gamma
-- name    : Formalism.FourierDecayAlt.P.Mx7.lowering_intertwine_gamma
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:33.860507+00:00
-- url     : https://prove2.me/theorems/7ce1cbda-a79a-4a0e-b61b-269c07c5b8fb
-- title:
--   Mx7: lowering intertwine gamma
-- statement:
--   The Mx7 construction uses the lowering intertwine gamma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L963-L975
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L963-L975

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
variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem Formalism.FourierDecayAlt.P.Mx7.lowering_intertwine_gamma (G Gi X L0 L1 U U' : R) (hLG : L0 * G = G * L1) (hXL : Commute X L1) (hUX : U * X = X * U')
    (hGU : Commute G U) (hGiX : Commute Gi X) (hGGi : Commute G Gi) :
    (L0 + Gi * U) * (G * X) = (G * X) * (L1 + Gi * U') := by sorry
