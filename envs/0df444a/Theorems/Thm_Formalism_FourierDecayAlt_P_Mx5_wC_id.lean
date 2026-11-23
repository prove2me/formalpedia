-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_wC_id
-- name    : Formalism.FourierDecayAlt.P.Mx5.wC_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:29:17.39537+00:00
-- url     : https://prove2.me/theorems/3fc53ebe-6f26-46b0-9fb9-5a04d3255f17
-- title:
--   Mx5: w C id
-- statement:
--   The Mx5 construction uses the w C id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L786-L805
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L786-L805

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

theorem Formalism.FourierDecayAlt.P.Mx5.wC_id (hP : P.OK) (π : Ty P) (Y : ℂ) (h1 : xC P π (Y + 1) ≠ 0) :
    wC P π Y = qC P Y * (xC P π (Y + 1))⁻¹ +
      ∑ l ∈ Icc 1 (P.k - 1), xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹ := by sorry
