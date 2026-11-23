-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_block_frame_conjugation_identity
-- name    : Formalism.FourierDecayAlt.P.Mx5.block_frame_conjugation_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:30.451854+00:00
-- url     : https://prove2.me/theorems/0d327f2c-9631-46af-92f2-c784af371808
-- title:
--   Mx5: block frame conjugation identity
-- statement:
--   The Mx5 construction uses the block frame conjugation identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L230-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L230-L242

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

theorem Formalism.FourierDecayAlt.P.Mx5.block_frame_conjugation_identity {R : Type*} [Ring R] [Algebra ℂ R] (g gi z N : R) (a e : ℂ) (h1 : g * gi = 1)
    (hN : N * g = g * N - e • z) (hzg : Commute z g) (hzgi : Commute z gi) :
    g * (-N - a • (z * gi)) * gi = -N - (a + e) • (gi * z) := by sorry
