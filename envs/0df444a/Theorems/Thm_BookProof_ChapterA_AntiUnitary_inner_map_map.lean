-- Prove2me | Theorems.Thm_BookProof_ChapterA_AntiUnitary_inner_map_map
-- name    : BookProof.ChapterA.AntiUnitary.inner_map_map
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T04:25:56.940866+00:00
-- url     : https://prove2.me/theorems/c7ec858a-77f0-4e2c-a9ba-fad13a61b021
-- title:
--   `BookProof.ChapterA.AntiUnitary.inner_map_map` (θ : AntiUnitary V) (x y : V) : inner ℂ (θ x) (θ y) = conj (inner ℂ x y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1`.
--
--   `BookProof.ChapterA.AntiUnitary.inner_map_map` (θ : AntiUnitary V) (x y : V) : inner ℂ (θ x) (θ y) = conj (inner ℂ x y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.AntiUnitary.inner_map_map`.

-- Generated from ChapterA1.lean — theorem BookProof.ChapterA.AntiUnitary.inner_map_map
import Mathlib
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

theorem BookProof.ChapterA.AntiUnitary.inner_map_map (θ : AntiUnitary V) (x y : V) :
    inner ℂ (θ x) (θ y) = conj (inner ℂ x y) := by sorry
