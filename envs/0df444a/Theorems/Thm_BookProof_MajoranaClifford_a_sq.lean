-- Prove2me | Theorems.Thm_BookProof_MajoranaClifford_a_sq
-- name    : BookProof.MajoranaClifford.a_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:06:18.242687+00:00
-- url     : https://prove2.me/theorems/8084e7fd-fa6f-47b4-8190-e48b6e121b33
-- title:
--   The Clifford relation** `a(v)² = ⟪v,v⟫·1`: the defining relation of the book's `C(V)`
-- statement:
--   **The Clifford relation** `a(v)² = ⟪v,v⟫·1`: the defining relation of the
--   book's `C(V)`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MajoranaClifford.a_sq` (module `BookProof.MajoranaClifford`), line-linked source: `ChapterMajoranaClifford.lean` lines 97–101.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaClifford.lean#L97-L101

-- Generated from ChapterMajoranaClifford.lean — theorem BookProof.MajoranaClifford.a_sq
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford









open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem BookProof.MajoranaClifford.a_sq (v : V) : a v * a v = algebraMap ℝ (CliffordAlgebra (Qform (V := V))) ⟪v, v⟫ := by sorry
