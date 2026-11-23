-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_sh_pair
-- name    : Formalism.FourierDecayAlt.P.Mx7.sh_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:42:06.250528+00:00
-- url     : https://prove2.me/theorems/602fdca0-a7c1-4cea-8754-924a9979246b
-- title:
--   Mx7: sh pair
-- statement:
--   The Mx7 construction uses the sh pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L86-L91

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

theorem Formalism.FourierDecayAlt.P.Mx7.sh_pair (hSh : SSShift) (hR : RhoUp) (P : Par) (l j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) (Y : ℂ) :
    (kap P fun π => xEx P {l} π Y) * SS P j = SS P j * kap P fun π => xEx P {l, j} π Y * (Y + 1 + (rho P π j : ℂ)) := by sorry
