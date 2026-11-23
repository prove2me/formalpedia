-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_witt_extension_of_nondeg_gram
-- name    : Formalism.FourierDecayAlt.P.S3x6.witt_extension_of_nondeg_gram
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:24.2008+00:00
-- url     : https://prove2.me/theorems/5cf46d6d-0242-4d51-9644-9056243b6684
-- title:
--   S3x6: witt extension of nondeg gram
-- statement:
--   The S3x6 construction uses the witt extension of nondeg gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L357-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L357-L391

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

theorem Formalism.FourierDecayAlt.P.S3x6.witt_extension_of_nondeg_gram (hσ : Inv σ) [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h)
    (hn : Nondeg h) {a : ℕ} (x y : Fin a → V) (hG : IsUnit (gramMatrix h x).det)
    (hxy : ∀ i j, h (x i) (x j) = h (y i) (y j)) :
    ∃ g : V ≃ₗ[K] V, (∀ u v, h (g u) (g v) = h u v) ∧ ∀ i, g (x i) = y i := by sorry
