-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_moduleH1Alt
-- name    : Formalism.FourierDecayAlt.P.Mx7.moduleH1Alt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:27.848731+00:00
-- url     : https://prove2.me/theorems/231ed0dd-f701-4f23-a748-4c6fd93e6d5c
-- title:
--   Mx7: module H1 Alt
-- statement:
--   The Mx7 construction uses the module H1 Alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L629-L647
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L629-L647

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

theorem Formalism.FourierDecayAlt.P.Mx7.moduleH1Alt (P : Par) (hP : P.OK) (π : Ty P) : ∀ l ∈ Icc 1 (P.k - 1),
    -((P.T : ℂ) * P.T') * (q1P P).eval (-(rho P π l : ℂ)) + (NrmDown P l π : ℂ) *
      ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-(rho P π l : ℂ) + (rho P π j : ℂ))) *
        ∏ j ∈ Icc 1 (P.k - 1), (-(rho P π l : ℂ) + ((rho P π j : ℂ) + 1))) = 0 := by sorry
