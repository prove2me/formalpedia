-- Prove2me | Theorems.Thm_BookProof_MajoranaClifford_reverse_antihom
-- name    : BookProof.MajoranaClifford.reverse_antihom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:54:48.366256+00:00
-- url     : https://prove2.me/theorems/2ac033d0-4a7b-4b4a-bc41-b11a6b9a2d9e
-- title:
--   The canonical involution `*` is an **anti-automorphism**: `(x·y)* = y*·x*`
-- statement:
--   The canonical involution `*` is an **anti-automorphism**:
--   `(x·y)* = y*·x*`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MajoranaClifford.reverse_antihom` (module `BookProof.MajoranaClifford`), line-linked source: `ChapterMajoranaClifford.lean` lines 123–127.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaClifford.lean#L123-L127

-- Generated from ChapterMajoranaClifford.lean — theorem BookProof.MajoranaClifford.reverse_antihom
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford









open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem BookProof.MajoranaClifford.reverse_antihom (x y : CliffordAlgebra (Qform (V := V))) :
    reverse (x * y) = reverse y * reverse x := by sorry
