-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_witt
-- name    : Formalism.FourierDecayAlt.P.S3x6.witt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:07.429809+00:00
-- url     : https://prove2.me/theorems/e744fa93-0b9e-428b-8646-d6648773a0fa
-- title:
--   S3x6: witt
-- statement:
--   The S3x6 construction uses the witt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L491-L498
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L491-L498

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

theorem Formalism.FourierDecayAlt.P.S3x6.witt (hσ : Inv σ) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h) (hn : Nondeg h) {a : ℕ} (x y : Fin a → V)
    (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, h (x i) (x j) = h (y i) (y j)) :
    ∃ g : V ≃ₗ[K] V, (∀ u v, h (g u) (g v) = h u v) ∧ ∀ i, g (x i) = y i := by sorry
