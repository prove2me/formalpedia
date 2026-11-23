-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absC
-- name    : Formalism.FourierDecayAlt.P.Mx7.absC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:33:48.706395+00:00
-- url     : https://prove2.me/theorems/6b7ce6aa-bdc1-4499-a95a-da8628a3eb4c
-- title:
--   Mx7: abs C
-- statement:
--   The Mx7 construction uses the abs C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L985-L1017
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L985-L1017

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

theorem Formalism.FourierDecayAlt.P.Mx7.absC (G Gi z zb N Ns K : R) (t : ℂ) (hGGi : G * Gi = 1) (hGdef : G = z * zb - algebraMap ℂ R t)
    (czzb : z * zb = zb * z) (cGiz : Gi * z = z * Gi) (cGizb : Gi * zb = zb * Gi)
    (nz : N * z = z * N + 1) (nGi : N * Gi = Gi * N - zb * Gi * Gi)
    (nszb : Ns * zb = zb * Ns - 1) (nsGi : Ns * Gi = Gi * Ns + z * Gi * Gi)
    (hcurv : Ns * N - N * Ns = K * Gi * Gi) (cu cv : ℂ) :
    (-Ns - cu • (z * Gi)) * (-N - cv • (zb * Gi)) - (-N - cv • (zb * Gi)) * (-Ns - cu • (z * Gi)) =
      K * Gi * Gi + ((cu + cv) * t) • (Gi * Gi) := by sorry
