-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_compC_off
-- name    : Formalism.FourierDecayAlt.P.Mx7.compC_off
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:01.603144+00:00
-- url     : https://prove2.me/theorems/2f600b5c-3415-4ff1-96fb-21b94ae434ad
-- title:
--   Mx7: comp C off
-- statement:
--   The Mx7 construction uses the comp C off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L241-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L241-L267

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

theorem Formalism.FourierDecayAlt.P.Mx7.compC_off (hSh : SSShift) (hC : SSComm) (hR : RhoUp) (P : Par) (hP : P.OK) (u v : ℂ) (l j : ℕ)
    (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    ((SS P l * kap P fun π => xEx P {l} π u) * (SS P j * kap P fun π => xEx P {j} π v) -
      (SS P l * kap P fun π => xEx P {l} π v) * (SS P j * kap P fun π => xEx P {j} π u)) +
    ((SS P j * kap P fun π => xEx P {j} π u) * (SS P l * kap P fun π => xEx P {l} π v) -
      (SS P j * kap P fun π => xEx P {j} π v) * (SS P l * kap P fun π => xEx P {l} π u)) = 0 := by sorry
