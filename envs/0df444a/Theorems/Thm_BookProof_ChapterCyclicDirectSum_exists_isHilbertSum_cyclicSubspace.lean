-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDirectSum_exists_isHilbertSum_cyclicSubspace
-- name    : BookProof.ChapterCyclicDirectSum.exists_isHilbertSum_cyclicSubspace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:08:46.471265+00:00
-- url     : https://prove2.me/theorems/73bd0e6f-ad9d-4a6a-88a6-97965da86097
-- title:
--   `BookProof.ChapterCyclicDirectSum.exists_isHilbertSum_cyclicSubspace` : ∃ S : Set H, OrthogonalCyclicFamily T hT S ∧ IsHilbertSum ℂ (fun x : S => (cyclicSubspace T hT (x : H))) (fu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDirectSum`.
--
--   `BookProof.ChapterCyclicDirectSum.exists_isHilbertSum_cyclicSubspace` : ∃ S : Set H, OrthogonalCyclicFamily T hT S ∧ IsHilbertSum ℂ (fun x : S => (cyclicSubspace T hT (x : H))) (fun x : S => (cyclicSubspace T hT (x : H)).subtypeₗᵢ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDirectSum.exists_isHilbertSum_cyclicSubspace`.

-- Generated from ChapterCyclicDirectSum.lean — theorem BookProof.ChapterCyclicDirectSum.exists_isHilbertSum_cyclicSubspace
import Definitions.Def_ChapterCyclicDecomposition
import Mathlib
import Definitions.Def_ChapterCyclicDirectSum
open BookProof.ChapterCyclicDirectSum


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterCyclicDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDirectSum.exists_isHilbertSum_cyclicSubspace :
    ∃ S : Set H, OrthogonalCyclicFamily T hT S ∧
      IsHilbertSum ℂ (fun x : S => (cyclicSubspace T hT (x : H)))
        (fun x : S => (cyclicSubspace T hT (x : H)).subtypeₗᵢ) := by sorry
