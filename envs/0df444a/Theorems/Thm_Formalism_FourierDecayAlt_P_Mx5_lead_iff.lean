-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_lead_iff
-- name    : Formalism.FourierDecayAlt.P.Mx5.lead_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:14.268656+00:00
-- url     : https://prove2.me/theorems/5b4792ba-63fb-4982-b0d7-ac91d0dab02e
-- title:
--   Mx5: lead iff
-- statement:
--   The Mx5 construction uses the lead iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L430-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L430-L447

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

theorem Formalism.FourierDecayAlt.P.Mx5.lead_iff (n : ℕ) (c : R) (f : ℂ → R) : Lead n c f ↔
    ∃ p : R[X], p.natDegree ≤ n ∧ p.coeff n = c ∧ ∀ Y, f Y = p.eval (algebraMap ℂ R Y) := by sorry
