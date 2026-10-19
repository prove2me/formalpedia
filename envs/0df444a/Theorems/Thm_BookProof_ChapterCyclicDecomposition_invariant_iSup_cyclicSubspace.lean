-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDecomposition_invariant_iSup_cyclicSubspace
-- name    : BookProof.ChapterCyclicDecomposition.invariant_iSup_cyclicSubspace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:39:24.777989+00:00
-- url     : https://prove2.me/theorems/3cf374d3-5b90-4eb0-9b5a-e05aa1ee4520
-- title:
--   `BookProof.ChapterCyclicDecomposition.invariant_iSup_cyclicSubspace` (S : Set H) : Invariant T hT (⨆ x ∈ S, cyclicSubspace T hT x).topologicalClosure
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDecomposition`.
--
--   `BookProof.ChapterCyclicDecomposition.invariant_iSup_cyclicSubspace` (S : Set H) : Invariant T hT (⨆ x ∈ S, cyclicSubspace T hT x).topologicalClosure
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDecomposition.invariant_iSup_cyclicSubspace`.

-- Generated from ChapterCyclicDecomposition.lean — theorem BookProof.ChapterCyclicDecomposition.invariant_iSup_cyclicSubspace
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
open BookProof.ChapterCyclicDecomposition


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDecomposition.invariant_iSup_cyclicSubspace (S : Set H) :
    Invariant T hT (⨆ x ∈ S, cyclicSubspace T hT x).topologicalClosure := by sorry
