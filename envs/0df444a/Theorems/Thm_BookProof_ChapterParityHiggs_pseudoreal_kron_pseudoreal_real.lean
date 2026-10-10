-- Prove2me | Theorems.Thm_BookProof_ChapterParityHiggs_pseudoreal_kron_pseudoreal_real
-- name    : BookProof.ChapterParityHiggs.pseudoreal_kron_pseudoreal_real
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:06:57.021108+00:00
-- url     : https://prove2.me/theorems/6c921bf2-1772-40f2-bb04-7fdc6bdc2faa
-- title:
--   `BookProof.ChapterParityHiggs.pseudoreal_kron_pseudoreal_real` {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : A *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParityHiggs`.
--
--   `BookProof.ChapterParityHiggs.pseudoreal_kron_pseudoreal_real` {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : A * A.map (starRingEnd ℂ) = -1) (hB : B * B.map (starRingEnd ℂ) = -1) : (A ⊗ₖ B) * ((A ⊗ₖ B).map (starRingEnd ℂ)) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParityHiggs.pseudoreal_kron_pseudoreal_real`.

-- Generated from ChapterParityHiggs.lean — theorem BookProof.ChapterParityHiggs.pseudoreal_kron_pseudoreal_real
import Definitions.Def_ChapterParity
import Mathlib
import Definitions.Def_ChapterParityHiggs
open BookProof.ChapterParityHiggs


open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

theorem BookProof.ChapterParityHiggs.pseudoreal_kron_pseudoreal_real
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (hA : A * A.map (starRingEnd ℂ) = -1) (hB : B * B.map (starRingEnd ℂ) = -1) :
    (A ⊗ₖ B) * ((A ⊗ₖ B).map (starRingEnd ℂ)) = 1 := by sorry
