-- Prove2me | Theorems.Thm_BookProof_ChapterA3_lorentz_of_conj
-- name    : BookProof.ChapterA3.lorentz_of_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:18:51.573411+00:00
-- url     : https://prove2.me/theorems/eb336f47-40cd-4263-884b-81bfacd9eff2
-- title:
--   `BookProof.ChapterA3.lorentz_of_conj` (S : Matrix (Fin 4) (Fin 4) ℂ) (hS : IsUnit S.det) (Lam : Matrix (Fin 4) (Fin 4) ℝ) (hLam : ∀ μ, S⁻¹ * mgamma μ * S = ∑ ν, (Lam μ ν : ℂ) • mga
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3b`.
--
--   `BookProof.ChapterA3.lorentz_of_conj` (S : Matrix (Fin 4) (Fin 4) ℂ) (hS : IsUnit S.det) (Lam : Matrix (Fin 4) (Fin 4) ℝ) (hLam : ∀ μ, S⁻¹ * mgamma μ * S = ∑ ν, (Lam μ ν : ℂ) • mgamma ν) : Lam * minkowskiMat * Lamᵀ = minkowskiMat
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.lorentz_of_conj`.

-- Generated from ChapterA3b.lean — theorem BookProof.ChapterA3.lorentz_of_conj
import Mathlib
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.lorentz_of_conj (S : Matrix (Fin 4) (Fin 4) ℂ) (hS : IsUnit S.det)
    (Lam : Matrix (Fin 4) (Fin 4) ℝ)
    (hLam : ∀ μ, S⁻¹ * mgamma μ * S = ∑ ν, (Lam μ ν : ℂ) • mgamma ν) :
    Lam * minkowskiMat * Lamᵀ = minkowskiMat := by sorry
