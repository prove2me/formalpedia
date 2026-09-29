-- Prove2me | Theorems.Thm_BookProof_MajoranaClifford_a_map_selfAdjoint
-- name    : BookProof.MajoranaClifford.a_map_selfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:06:58.32883+00:00
-- url     : https://prove2.me/theorems/31f7fd4e-e16a-4eab-8076-4b86df14b80c
-- title:
--   Symmetries act as real representations preserving self-adjointness.** For *any* real linear operator `T : V → V`, the transformed field operator `a(T v)` is again self-adjoint, so the map
-- statement:
--   **Symmetries act as real representations preserving self-adjointness.**  For
--   *any* real linear operator `T : V → V`, the transformed field operator `a(T v)`
--   is again self-adjoint, so the map `a(v) → a(T v)` preserves the
--   self-adjointness condition (the book's statement that the symmetry group acts by
--   real representations, `a(v) → a(T v)` with `T` a real operator).
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MajoranaClifford.a_map_selfAdjoint` (module `BookProof.MajoranaClifford`), line-linked source: `ChapterMajoranaClifford.lean` lines 135–141.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaClifford.lean#L135-L141

-- Generated from ChapterMajoranaClifford.lean — theorem BookProof.MajoranaClifford.a_map_selfAdjoint
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford









open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem BookProof.MajoranaClifford.a_map_selfAdjoint (T : V →ₗ[ℝ] V) (v : V) : reverse (a (T v)) = a (T v) := by sorry
