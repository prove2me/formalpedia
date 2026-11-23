-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_compB
-- name    : Formalism.FourierDecayAlt.P.Mx7.compB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:17.121873+00:00
-- url     : https://prove2.me/theorems/c00157ad-edc5-4d32-b0d2-0b62607c8508
-- title:
--   Mx7: comp B
-- statement:
--   The Mx7 construction uses the comp B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L206-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L206-L233

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

theorem Formalism.FourierDecayAlt.P.Mx7.compB (hSc : SSScalar) (hSh : SSShift) (hN : NabSS) (hR : RhoUp) (P : Par) (u v : ℂ) (l : ℕ)
    (hl : l ∈ Icc 1 (P.k - 1)) :
    (ggA P * xA P u * l0A P u) * (SS P l * kap P fun π => xEx P {l} π v) +
      (SS P l * kap P fun π => xEx P {l} π u) * (ggA P * xA P v * l0A P v) =
    (ggA P * xA P v * l0A P v) * (SS P l * kap P fun π => xEx P {l} π u) +
      (SS P l * kap P fun π => xEx P {l} π v) * (ggA P * xA P u * l0A P u) := by sorry
