-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul_const
-- name    : Formalism.FourierDecayAlt.P.Mx5.Lead.mul_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:13:16.064297+00:00
-- url     : https://prove2.me/theorems/d68fe70f-1200-478a-bc6c-e4ef7ebfdc1b
-- title:
--   Lead: mul const
-- statement:
--   The Lead construction uses the mul const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L495-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L495-L497

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
variable {R : Type*} [Ring R] [Algebra ℂ R]
variable {n m : ℕ} {c d : R} {f g : ℂ → R}

theorem Formalism.FourierDecayAlt.P.Mx5.Lead.mul_const (a : R) (hf : Lead n c f) : Lead n (c * a) fun Y => f Y * a := by sorry
