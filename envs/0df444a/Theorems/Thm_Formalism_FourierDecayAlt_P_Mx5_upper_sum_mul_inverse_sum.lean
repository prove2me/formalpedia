-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_upper_sum_mul_inverse_sum
-- name    : Formalism.FourierDecayAlt.P.Mx5.upper_sum_mul_inverse_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:29:08.844498+00:00
-- url     : https://prove2.me/theorems/263dda2c-817a-404e-90b0-2f19590dd8a5
-- title:
--   Mx5: upper sum mul inverse sum
-- statement:
--   The Mx5 construction uses the upper sum mul inverse sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L857-L867
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L857-L867

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

theorem Formalism.FourierDecayAlt.P.Mx5.upper_sum_mul_inverse_sum (hN : ∀ l ∈ Icc 1 (P.k - 1), star (SS P l) * SS P l = kap P fun π => ((Nrm P l π : ℝ) : ℂ))
    (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) :
    S12 P Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j =
      (kap P fun π => ∑ l ∈ Icc 1 (P.k - 1),
        xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹) + S4 P Y := by sorry
