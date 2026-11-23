-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_xC_split
-- name    : Formalism.FourierDecayAlt.P.Mx5.xC_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:12:42.868962+00:00
-- url     : https://prove2.me/theorems/786194fa-5a38-4225-962c-e3330b052a48
-- title:
--   Mx5: x C split
-- statement:
--   The Mx5 construction uses the x C split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L706-L710
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L706-L710

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

theorem Formalism.FourierDecayAlt.P.Mx5.xC_split (j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (π : Ty P) (Y : ℂ) :
    xC P π Y = (Y + (rho P π j : ℂ)) * xEx P {j} π Y := by sorry
