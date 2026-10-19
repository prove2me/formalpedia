-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDecomposition_cyclicSubspace_le_orthogonal
-- name    : BookProof.ChapterCyclicDecomposition.cyclicSubspace_le_orthogonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:38:29.175095+00:00
-- url     : https://prove2.me/theorems/4a1be9ad-51e8-4a20-a3f3-51a97dc5d353
-- title:
--   `BookProof.ChapterCyclicDecomposition.cyclicSubspace_le_orthogonal` {M : Submodule ℂ H} (hM : Invariant T hT M) {v : H} (hv : v ∈ Mᗮ) : cyclicSubspace T hT v ≤ Mᗮ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDecomposition`.
--
--   `BookProof.ChapterCyclicDecomposition.cyclicSubspace_le_orthogonal` {M : Submodule ℂ H} (hM : Invariant T hT M) {v : H} (hv : v ∈ Mᗮ) : cyclicSubspace T hT v ≤ Mᗮ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDecomposition.cyclicSubspace_le_orthogonal`.

-- Generated from ChapterCyclicDecomposition.lean — theorem BookProof.ChapterCyclicDecomposition.cyclicSubspace_le_orthogonal
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
open BookProof.ChapterCyclicDecomposition


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDecomposition.cyclicSubspace_le_orthogonal {M : Submodule ℂ H} (hM : Invariant T hT M) {v : H}
    (hv : v ∈ Mᗮ) : cyclicSubspace T hT v ≤ Mᗮ := by sorry
