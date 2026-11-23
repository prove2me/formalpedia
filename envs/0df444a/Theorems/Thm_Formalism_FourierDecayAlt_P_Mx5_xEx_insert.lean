-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_xEx_insert
-- name    : Formalism.FourierDecayAlt.P.Mx5.xEx_insert
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:29:41.366876+00:00
-- url     : https://prove2.me/theorems/36aef812-ac4d-4b65-a19a-8de6cec1baa0
-- title:
--   Mx5: x Ex insert
-- statement:
--   The Mx5 construction uses the x Ex insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L712-L716
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L712-L716

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)

theorem Formalism.FourierDecayAlt.P.Mx5.xEx_insert (ex : Finset ℕ) (a : ℕ) (ha : a ∈ Icc 1 (P.k - 1) \ ex) (π : Ty P) (Y : ℂ) :
    xEx P ex π Y = (Y + (rho P π a : ℂ)) * xEx P (insert a ex) π Y := by sorry
