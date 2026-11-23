-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_exists_isotropic_completion
-- name    : Formalism.FourierDecayAlt.P.S3x6.exists_isotropic_completion
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:22.983549+00:00
-- url     : https://prove2.me/theorems/923631d1-0555-4f69-9f0d-addbb7be13b7
-- title:
--   S3x6: exists isotropic completion
-- statement:
--   The S3x6 construction uses the exists isotropic completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L393-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L393-L431

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

theorem Formalism.FourierDecayAlt.P.S3x6.exists_isotropic_completion (hσ : Inv σ) (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h) (hn : Nondeg h) {a : ℕ}
    (x : Fin a → V) (hx : LinearIndependent K x) (N : Fin a → K) (i0 : Fin a) (hN : N i0 ≠ 0)
    (hGN : ∀ i, h (x i) (∑ j, N j • x j) = 0) :
    ∃ m, (∀ i, h (x i) m = if i = i0 then 1 else 0) ∧ h m m = 0 ∧
      m ∉ Submodule.span K (Set.range x) := by sorry
