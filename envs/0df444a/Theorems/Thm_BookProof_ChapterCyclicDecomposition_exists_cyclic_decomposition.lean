-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDecomposition_exists_cyclic_decomposition
-- name    : BookProof.ChapterCyclicDecomposition.exists_cyclic_decomposition
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:39:11.6884+00:00
-- url     : https://prove2.me/theorems/69a98b7f-648d-460d-b5de-c08303bf47b8
-- title:
--   `BookProof.ChapterCyclicDecomposition.exists_cyclic_decomposition` : ∃ S : Set H, OrthogonalCyclicFamily T hT S ∧ (⨆ x ∈ S, cyclicSubspace T hT x).topologicalClosure = ⊤
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDecomposition`.
--
--   `BookProof.ChapterCyclicDecomposition.exists_cyclic_decomposition` : ∃ S : Set H, OrthogonalCyclicFamily T hT S ∧ (⨆ x ∈ S, cyclicSubspace T hT x).topologicalClosure = ⊤
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDecomposition.exists_cyclic_decomposition`.

-- Generated from ChapterCyclicDecomposition.lean — theorem BookProof.ChapterCyclicDecomposition.exists_cyclic_decomposition
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
open BookProof.ChapterCyclicDecomposition


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDecomposition.exists_cyclic_decomposition :
    ∃ S : Set H, OrthogonalCyclicFamily T hT S ∧
      (⨆ x ∈ S, cyclicSubspace T hT x).topologicalClosure = ⊤ := by sorry
