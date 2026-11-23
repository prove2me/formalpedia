-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_weighted_sum_difference_identity
-- name    : Formalism.FourierDecayAlt.P.Mx7.weighted_sum_difference_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:04.143987+00:00
-- url     : https://prove2.me/theorems/c682eeb2-b553-47de-9fb0-9d24bd638aed
-- title:
--   Mx7: weighted sum difference identity
-- statement:
--   The Mx7 construction uses the weighted sum difference identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L136-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L136-L145

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

theorem Formalism.FourierDecayAlt.P.Mx7.weighted_sum_difference_identity (G b N S X Xp E : R) (hNS : N * S = S * N - b * S) (hbS : b * S = S * b)
    (hXS : X * S = S * Xp) (hSG : S * G = G * S) (hEN : Commute E N) (hEb : Commute E b) (c : ℂ) :
    G * X * (-N - c • b) * (S * E) = S * G * (Xp * E * ((-N - c • b) + b)) := by sorry
