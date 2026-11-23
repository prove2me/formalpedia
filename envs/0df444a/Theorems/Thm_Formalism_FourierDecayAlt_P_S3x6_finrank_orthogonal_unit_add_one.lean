-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_finrank_orthogonal_unit_add_one
-- name    : Formalism.FourierDecayAlt.P.S3x6.finrank_orthogonal_unit_add_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:11.989699+00:00
-- url     : https://prove2.me/theorems/7927a6b0-d73e-427f-9a29-55fee2cff9fc
-- title:
--   S3x6: finrank orthogonal unit add one
-- statement:
--   The S3x6 construction uses the finrank orthogonal unit add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L51-L57

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V]

theorem Formalism.FourierDecayAlt.P.S3x6.finrank_orthogonal_unit_add_one [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K) (v : V) (hv : h v v = 1) :
    finrank K (LinearMap.ker (h v)) + 1 = finrank K V := by sorry
