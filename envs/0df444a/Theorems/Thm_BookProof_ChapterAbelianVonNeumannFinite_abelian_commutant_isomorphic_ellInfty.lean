-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianVonNeumannFinite_abelian_commutant_isomorphic_ellInfty
-- name    : BookProof.ChapterAbelianVonNeumannFinite.abelian_commutant_isomorphic_ellInfty
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:51:47.004494+00:00
-- url     : https://prove2.me/theorems/e23e76ac-4897-4f60-9f64-597376db12ac
-- title:
--   `BookProof.ChapterAbelianVonNeumannFinite.abelian_commutant_isomorphic_ellInfty` {A : Matrix n n ℂ} (hA : A.IsHermitian) (hdist : Function.Injective hA.eigenvalues) : ∃ f : (n → ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianVonNeumannFinite`.
--
--   `BookProof.ChapterAbelianVonNeumannFinite.abelian_commutant_isomorphic_ellInfty` {A : Matrix n n ℂ} (hA : A.IsHermitian) (hdist : Function.Injective hA.eigenvalues) : ∃ f : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ, Function.Injective f ∧ Set.range f = {M : Matrix n n ℂ | M * A = A * M}
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianVonNeumannFinite.abelian_commutant_isomorphic_ellInfty`.

-- Generated from ChapterAbelianVonNeumannFinite.lean — theorem BookProof.ChapterAbelianVonNeumannFinite.abelian_commutant_isomorphic_ellInfty
import Mathlib
import Definitions.Def_ChapterAbelianVonNeumannFinite
open BookProof.ChapterAbelianVonNeumannFinite


open Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterAbelianVonNeumannFinite.abelian_commutant_isomorphic_ellInfty {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hdist : Function.Injective hA.eigenvalues) :
    ∃ f : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ,
      Function.Injective f ∧ Set.range f = {M : Matrix n n ℂ | M * A = A * M} := by sorry
