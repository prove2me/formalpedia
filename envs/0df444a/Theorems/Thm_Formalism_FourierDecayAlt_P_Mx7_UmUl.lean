-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_UmUl
-- name    : Formalism.FourierDecayAlt.P.Mx7.UmUl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:33:39.263564+00:00
-- url     : https://prove2.me/theorems/19472ecf-8cd7-4df9-8df6-3d0405fea046
-- title:
--   Mx7: Um Ul
-- statement:
--   The Mx7 construction uses the Um Ul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1339-L1349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1339-L1349

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

theorem Formalism.FourierDecayAlt.P.Mx7.UmUl (hSh : SSShift) (hR : RhoUp) (hNorm : SSNorm) (hMix : SSMixed) (P : Par) (hP : P.OK) (u : ℂ) :
    Um P u * Ul P u - Ul P u * Um P u =
      kap P fun π => ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
        (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) := by sorry
