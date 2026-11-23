-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isSymplectic_of_eight_relations
-- name    : Formalism.FourierDecayAlt.P.Mx7.isSymplectic_of_eight_relations
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:50.650944+00:00
-- url     : https://prove2.me/theorems/bf3e9ee0-7f82-4854-9d2c-e091ce77c4ee
-- title:
--   Mx7: is Symplectic of eight relations
-- statement:
--   The Mx7 construction uses the is Symplectic of eight relations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L932-L949
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L932-L949

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
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
variable {B : Type} [Ring B] [Algebra ℂ B]
open Matrix

theorem Formalism.FourierDecayAlt.P.Mx7.isSymplectic_of_eight_relations (a b c d a' b' c' d' q : B)
    (e1 : a' * c - c' * a = 0) (e2 : a' * d - c' * b = q) (e3 : b' * c - d' * a = -q) (e4 : b' * d - d' * b = 0)
    (e5 : a * b' - b * a' = 0) (e6 : a * d' - b * c' = q) (e7 : c * b' - d * a' = -q) (e8 : c * d' - d * c' = 0) :
    (!![a', b'; c', d'] : Matrix (Fin 2) (Fin 2) B)ᵀ * Formalism.YangianSpanCharacter.T.J B * !![a, b; c, d] = q • Formalism.YangianSpanCharacter.T.J B ∧
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) B) * Formalism.YangianSpanCharacter.T.J B * (!![a', b'; c', d'] : Matrix (Fin 2) (Fin 2) B)ᵀ = q • Formalism.YangianSpanCharacter.T.J B := by sorry
