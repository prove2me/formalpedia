-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xEx_pair
-- name    : Formalism.FourierDecayAlt.P.Mx7.xEx_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:18.826888+00:00
-- url     : https://prove2.me/theorems/62766d5c-698d-4903-a2f9-233d23b7be91
-- title:
--   Mx7: x Ex pair
-- statement:
--   The Mx7 construction uses the x Ex pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L45-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L45-L56

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

theorem Formalism.FourierDecayAlt.P.Mx7.xEx_pair (P : Par) (π : Ty P) (Y : ℂ) (l j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    xEx P {l} π Y = xEx P {l, j} π Y * (Y + (rho P π j : ℂ)) := by sorry
