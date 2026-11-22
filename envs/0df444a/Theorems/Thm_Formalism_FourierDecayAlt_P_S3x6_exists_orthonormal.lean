-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_exists_orthonormal
-- name    : Formalism.FourierDecayAlt.P.S3x6.exists_orthonormal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:37.473932+00:00
-- url     : https://prove2.me/theorems/a8bc88f0-280e-4a0f-aacb-fc8d0dc21c3f
-- title:
--   S3x6: exists orthonormal
-- statement:
--   The S3x6 construction uses the exists orthonormal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L111-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L111-L139

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

theorem Formalism.FourierDecayAlt.P.S3x6.exists_orthonormal (hσ : Inv σ) (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K), Herm h → Nondeg h → finrank K V = n →
    ∃ b : Basis (Fin n) K V, Ortho h b := by sorry
