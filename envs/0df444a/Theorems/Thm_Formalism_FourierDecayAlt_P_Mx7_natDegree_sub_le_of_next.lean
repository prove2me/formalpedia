-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_natDegree_sub_le_of_next
-- name    : Formalism.FourierDecayAlt.P.Mx7.natDegree_sub_le_of_next
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:21.450419+00:00
-- url     : https://prove2.me/theorems/d16f3173-915e-4ea3-aa5d-e96da7e0d85b
-- title:
--   Mx7: nat Degree sub le of next
-- statement:
--   The Mx7 construction uses the nat Degree sub le of next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L308-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L308-L324

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
noncomputable section

theorem Formalism.FourierDecayAlt.P.Mx7.natDegree_sub_le_of_next (p1 p2 : ℂ[X]) (N : ℕ) (h1 : p1.Monic) (h2 : p2.Monic)
    (d1 : p1.natDegree = N + 2) (d2 : p2.natDegree = N + 2) (hn : p1.nextCoeff = p2.nextCoeff) :
    (p1 - p2).natDegree ≤ N := by sorry
