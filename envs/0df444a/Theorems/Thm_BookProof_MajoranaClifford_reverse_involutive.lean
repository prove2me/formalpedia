-- Prove2me | Theorems.Thm_BookProof_MajoranaClifford_reverse_involutive
-- name    : BookProof.MajoranaClifford.reverse_involutive
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:55:26.70685+00:00
-- url     : https://prove2.me/theorems/a226d3bb-2015-4853-8141-5b08a0fff755
-- title:
--   The canonical involution `*` is **of order two** (`** = id`), hence a genuine involution
-- statement:
--   The canonical involution `*` is **of order two** (`** = id`), hence a genuine
--   involution.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MajoranaClifford.reverse_involutive` (module `BookProof.MajoranaClifford`), line-linked source: `ChapterMajoranaClifford.lean` lines 129–133.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaClifford.lean#L129-L133

-- Generated from ChapterMajoranaClifford.lean — theorem BookProof.MajoranaClifford.reverse_involutive
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford









open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem BookProof.MajoranaClifford.reverse_involutive :
    Function.Involutive (reverse : CliffordAlgebra (Qform (V := V)) → _) := by sorry
