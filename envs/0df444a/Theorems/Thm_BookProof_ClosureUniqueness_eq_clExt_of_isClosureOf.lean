-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_eq_clExt_of_isClosureOf
-- name    : BookProof.ClosureUniqueness.eq_clExt_of_isClosureOf
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:38:13.251525+00:00
-- url     : https://prove2.me/theorems/4f68ffe9-50d9-4850-9848-d2f0b4aa8ed2
-- title:
--   `BookProof.ClosureUniqueness.eq_clExt_of_isClosureOf` {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (hA : IsClosureOf T A) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) : Dom = clDom T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.eq_clExt_of_isClosureOf` {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (hA : IsClosureOf T A) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) : Dom = clDom T ∧ ∀ (x : F) (h₁ : x ∈ Dom) (h₂ : x ∈ clDom T), A ⟨x, h₁⟩ = clExt T hdense hsym ⟨x, h₂⟩
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.eq_clExt_of_isClosureOf`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.eq_clExt_of_isClosureOf
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.eq_clExt_of_isClosureOf {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (hA : IsClosureOf T A)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) :
    Dom = clDom T ∧ ∀ (x : F) (h₁ : x ∈ Dom) (h₂ : x ∈ clDom T),
      A ⟨x, h₁⟩ = clExt T hdense hsym ⟨x, h₂⟩ := by sorry
