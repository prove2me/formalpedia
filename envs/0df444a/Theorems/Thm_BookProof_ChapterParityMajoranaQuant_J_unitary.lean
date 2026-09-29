-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_J_unitary
-- name    : BookProof.ChapterParityMajoranaQuant.J_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:47:30.73472+00:00
-- url     : https://prove2.me/theorems/4b165178-c95d-4507-a971-f423d429ed47
-- title:
--   A compatible complex structure is **unitary**: `Jᴴ · J = 1`
-- statement:
--   A compatible complex structure is **unitary**: `Jᴴ · J = 1`.  On a real inner-product
--   space, a skew-symmetric `J` with `J² = -1` is orthogonal, so it preserves the metric — the
--   compatibility of the metric, the complex structure and the symplectic form `⟨v,Jw⟩`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.J_unitary` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 144–148.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L144-L148

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.J_unitary
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.J_unitary (hJ2 : J * J = -1) (hskew : Jᴴ = -J) : Jᴴ * J = 1 := by sorry
