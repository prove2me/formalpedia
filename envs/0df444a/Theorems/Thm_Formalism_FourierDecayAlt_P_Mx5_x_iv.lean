-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_x_iv
-- name    : Formalism.FourierDecayAlt.P.Mx5.x_iv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:16:26.579797+00:00
-- url     : https://prove2.me/theorems/24c6e140-7789-467e-b27c-e6e5907df78d
-- title:
--   Mx5: x iv
-- statement:
--   The Mx5 construction uses the x iv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L723-L729
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L723-L729

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

theorem Formalism.FourierDecayAlt.P.Mx5.x_iv (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) (j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) :
    xA P Y * (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) = kap P fun π => xEx P {j} π Y := by sorry
