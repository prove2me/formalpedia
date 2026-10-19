-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDecomposition_invariant_orthogonal
-- name    : BookProof.ChapterCyclicDecomposition.invariant_orthogonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:38:21.622072+00:00
-- url     : https://prove2.me/theorems/b046de26-cb21-4e70-86fe-6b51ac93a084
-- title:
--   `BookProof.ChapterCyclicDecomposition.invariant_orthogonal` {M : Submodule ℂ H} (hM : Invariant T hT M) : Invariant T hT Mᗮ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDecomposition`.
--
--   `BookProof.ChapterCyclicDecomposition.invariant_orthogonal` {M : Submodule ℂ H} (hM : Invariant T hT M) : Invariant T hT Mᗮ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDecomposition.invariant_orthogonal`.

-- Generated from ChapterCyclicDecomposition.lean — theorem BookProof.ChapterCyclicDecomposition.invariant_orthogonal
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
open BookProof.ChapterCyclicDecomposition


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDecomposition.invariant_orthogonal {M : Submodule ℂ H} (hM : Invariant T hT M) :
    Invariant T hT Mᗮ := by sorry
