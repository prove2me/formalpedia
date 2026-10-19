-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDirectSum_hasSum_starProjection_cyclicSubspace
-- name    : BookProof.ChapterCyclicDirectSum.hasSum_starProjection_cyclicSubspace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:09:26.560977+00:00
-- url     : https://prove2.me/theorems/12530ac6-1cf3-4919-952d-03f576647325
-- title:
--   `BookProof.ChapterCyclicDirectSum.hasSum_starProjection_cyclicSubspace` {S : Set H} (hS : OrthogonalCyclicFamily T hT S) (htop : (⨆ x ∈ S, cyclicSubspace T hT x).topologicalClosure
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDirectSum`.
--
--   `BookProof.ChapterCyclicDirectSum.hasSum_starProjection_cyclicSubspace` {S : Set H} (hS : OrthogonalCyclicFamily T hT S) (htop : (⨆ x ∈ S, cyclicSubspace T hT x).topologicalClosure = ⊤) (v : H) : HasSum (fun x : S => (cyclicSubspace T hT (x : H)).starProjection v) v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDirectSum.hasSum_starProjection_cyclicSubspace`.

-- Generated from ChapterCyclicDirectSum.lean — theorem BookProof.ChapterCyclicDirectSum.hasSum_starProjection_cyclicSubspace
import Definitions.Def_ChapterCyclicDecomposition
import Mathlib
import Definitions.Def_ChapterCyclicDirectSum
open BookProof.ChapterCyclicDirectSum


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterCyclicDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDirectSum.hasSum_starProjection_cyclicSubspace {S : Set H} (hS : OrthogonalCyclicFamily T hT S)
    (htop : (⨆ x ∈ S, cyclicSubspace T hT x).topologicalClosure = ⊤) (v : H) :
    HasSum (fun x : S => (cyclicSubspace T hT (x : H)).starProjection v) v := by sorry
