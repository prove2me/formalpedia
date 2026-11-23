-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_norm_orthonormal_coords
-- name    : Formalism.FourierDecayAlt.P.S3x6.form_norm_orthonormal_coords
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:06.266215+00:00
-- url     : https://prove2.me/theorems/177ac051-9c2d-4b7c-85c2-70379934bf83
-- title:
--   S3x6: form norm orthonormal coords
-- statement:
--   The S3x6 construction uses the form norm orthonormal coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L141-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L141-L147

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

theorem Formalism.FourierDecayAlt.P.S3x6.form_norm_orthonormal_coords {V : Type} [AddCommGroup V] [Module K V] {h : V →ₛₗ[σ] V →ₗ[K] K} {n : ℕ}
    (b : Basis (Fin n) K V) (hb : Ortho h b) (v : V) :
    h v v = ∑ i, σ (b.equivFun v i) * b.equivFun v i := by sorry
