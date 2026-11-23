-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_diag_term
-- name    : Formalism.FourierDecayAlt.P.Mx5.diag_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:24.152807+00:00
-- url     : https://prove2.me/theorems/921b0b41-f7e1-4078-8bcc-69e9be076fff
-- title:
--   Mx5: diag term
-- statement:
--   The Mx5 construction uses the diag term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L829-L842
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L829-L842

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

theorem Formalism.FourierDecayAlt.P.Mx5.diag_term {l : ℕ} (hN : star (SS P l) * SS P l = kap P fun π => ((Nrm P l π : ℝ) : ℂ)) (Y : ℂ)
    (hl : l ∈ Icc 1 (P.k - 1)) :
    (kap P fun π => xEx P {l} π Y) * star (SS P l) * ((kap P fun π => (Y + (rho P π l : ℂ))⁻¹) * SS P l) =
      kap P fun π => xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹ := by sorry
