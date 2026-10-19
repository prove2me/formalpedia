-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_rangeClosure_invariant
-- name    : BookProof.ChapterSchurIrreducible.rangeClosure_invariant
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T01:01:06.241491+00:00
-- url     : https://prove2.me/theorems/f24ed71c-836f-4150-99fc-0aa90d916f3a
-- title:
--   `BookProof.ChapterSchurIrreducible.rangeClosure_invariant` {F m : V →L[ℂ] V} (hc : Commute F m) {w : V} (hw : w ∈ rangeClosure F) : m w ∈ rangeClosure F
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.rangeClosure_invariant` {F m : V →L[ℂ] V} (hc : Commute F m) {w : V} (hw : w ∈ rangeClosure F) : m w ∈ rangeClosure F
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.rangeClosure_invariant`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.rangeClosure_invariant
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.rangeClosure_invariant {F m : V →L[ℂ] V} (hc : Commute F m) {w : V}
    (hw : w ∈ rangeClosure F) : m w ∈ rangeClosure F := by sorry
