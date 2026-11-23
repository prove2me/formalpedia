-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_commutator_perturbed_product
-- name    : Formalism.FourierDecayAlt.P.Mx7.commutator_perturbed_product
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:43.665909+00:00
-- url     : https://prove2.me/theorems/c8af0695-06f9-41ca-8716-1e7ef0a154ee
-- title:
--   Mx7: commutator perturbed product
-- statement:
--   The Mx7 construction uses the commutator perturbed product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1019-L1033
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1019-L1033

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
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem Formalism.FourierDecayAlt.P.Mx7.commutator_perturbed_product (M0 L0 Gi Sl Sm : R) (hA : Commute M0 (Gi * Sl)) (hB : Commute L0 (Gi * Sm))
    (hGm : Commute Gi Sm) (hGl : Commute Gi Sl) :
    (M0 + Gi * Sm) * (L0 + Gi * Sl) - (L0 + Gi * Sl) * (M0 + Gi * Sm) =
      (M0 * L0 - L0 * M0) + Gi * Gi * (Sm * Sl - Sl * Sm) := by sorry
