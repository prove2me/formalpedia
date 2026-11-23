-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_conj_eq_of_nonneg_real
-- name    : Formalism.FourierDecayAlt.P.Mx5.conj_eq_of_nonneg_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:22.468712+00:00
-- url     : https://prove2.me/theorems/d2c332fb-f9c8-458d-8232-ae2beb14c82b
-- title:
--   Mx5: conj eq of nonneg real
-- statement:
--   The Mx5 construction uses the conj eq of nonneg real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L380-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean#L380-L390

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

theorem Formalism.FourierDecayAlt.P.Mx5.conj_eq_of_nonneg_real {R : Type*} [Ring R] (g gi x M L : R) (h2 : gi * g = 1)
    (e1 : gi * (x * g) = x) (hxM : Commute x M) (hxL : Commute x L) :
    g * M * gi * (g * L * gi * (x * g)) = g * x * M * L := by sorry
