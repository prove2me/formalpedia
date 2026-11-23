-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_double_root_of_adjacent_rho
-- name    : Formalism.FourierDecayAlt.P.Mx7.double_root_of_adjacent_rho
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:05.042149+00:00
-- url     : https://prove2.me/theorems/8bff95b3-8238-4f60-a379-2cabbca1faf5
-- title:
--   Mx7: double root of adjacent rho
-- statement:
--   The Mx7 construction uses the double root of adjacent rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L670-L700
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L670-L700

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

theorem Formalism.FourierDecayAlt.P.Mx7.double_root_of_adjacent_rho (P : Par) (hP : P.OK) (π : Ty P) : ∀ l ∈ Icc 1 (P.k - 1), ∀ m ∈ Icc 1 (P.k - 1),
    (rho P π m : ℂ) = (rho P π l : ℂ) + 1 → (Nrm P l π : ℂ) = 0 ∧ (NrmDown P m π : ℂ) = 0 ∧
      (X + C ((rho P π l : ℂ) + 1)) * (X + C ((rho P π l : ℂ) + 1)) ∣ q1P P := by sorry
