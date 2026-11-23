-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_extend_to_orthogonal_basis
-- name    : Formalism.FourierDecayAlt.P.S3x6.extend_to_orthogonal_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:20.006271+00:00
-- url     : https://prove2.me/theorems/8e51cdda-c7bc-4cb5-9e83-cea5a5edc5d5
-- title:
--   S3x6: extend to orthogonal basis
-- statement:
--   The S3x6 construction uses the extend to orthogonal basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L275-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L275-L355

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

theorem Formalism.FourierDecayAlt.P.S3x6.extend_to_orthogonal_basis (hσ : Inv σ) [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h)
    (hn : Nondeg h) {a : ℕ} (x : Fin a → V) (hG : IsUnit (gramMatrix h x).det) :
    ∃ b : Basis (Fin a ⊕ Fin (finrank K V - a)) K V, (∀ i, b (Sum.inl i) = x i) ∧
      (∀ i j, h (b (Sum.inl i)) (b (Sum.inr j)) = 0) ∧
      (∀ i j, h (b (Sum.inr j)) (b (Sum.inl i)) = 0) ∧
      ∀ j k, h (b (Sum.inr j)) (b (Sum.inr k)) = if j = k then 1 else 0 := by sorry
