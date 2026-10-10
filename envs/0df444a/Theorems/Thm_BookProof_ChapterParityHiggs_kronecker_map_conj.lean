-- Prove2me | Theorems.Thm_BookProof_ChapterParityHiggs_kronecker_map_conj
-- name    : BookProof.ChapterParityHiggs.kronecker_map_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:06:46.392975+00:00
-- url     : https://prove2.me/theorems/74e47697-564d-426a-ae41-8bee09e83599
-- title:
--   `BookProof.ChapterParityHiggs.kronecker_map_conj` {l m n p : Type*} (A : Matrix l m ℂ) (B : Matrix n p ℂ) : (A ⊗ₖ B).map (starRingEnd ℂ) = (A.map (starRingEnd ℂ)) ⊗ₖ (B.map (starRi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParityHiggs`.
--
--   `BookProof.ChapterParityHiggs.kronecker_map_conj` {l m n p : Type*} (A : Matrix l m ℂ) (B : Matrix n p ℂ) : (A ⊗ₖ B).map (starRingEnd ℂ) = (A.map (starRingEnd ℂ)) ⊗ₖ (B.map (starRingEnd ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParityHiggs.kronecker_map_conj`.

-- Generated from ChapterParityHiggs.lean — theorem BookProof.ChapterParityHiggs.kronecker_map_conj
import Definitions.Def_ChapterParity
import Mathlib
import Definitions.Def_ChapterParityHiggs
open BookProof.ChapterParityHiggs


open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

theorem BookProof.ChapterParityHiggs.kronecker_map_conj {l m n p : Type*} (A : Matrix l m ℂ) (B : Matrix n p ℂ) :
    (A ⊗ₖ B).map (starRingEnd ℂ)
      = (A.map (starRingEnd ℂ)) ⊗ₖ (B.map (starRingEnd ℂ)) := by sorry
