-- Prove2me | Theorems.Thm_BookProof_ChapterRadialLaplacian_hasFDerivAt_normSq
-- name    : BookProof.ChapterRadialLaplacian.hasFDerivAt_normSq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T22:57:45.161166+00:00
-- url     : https://prove2.me/theorems/46d18a09-53ee-48a1-bda1-6d356741bf46
-- title:
--   `BookProof.ChapterRadialLaplacian.hasFDerivAt_normSq` (x : E) : HasFDerivAt (fun z : E => ‖z‖ ^ 2) ((2 : ℝ) • innerCLM E x) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialLaplacian`.
--
--   `BookProof.ChapterRadialLaplacian.hasFDerivAt_normSq` (x : E) : HasFDerivAt (fun z : E => ‖z‖ ^ 2) ((2 : ℝ) • innerCLM E x) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRadialLaplacian.hasFDerivAt_normSq`.

-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.hasFDerivAt_normSq
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterRadialLaplacian.hasFDerivAt_normSq (x : E) :
    HasFDerivAt (fun z : E => ‖z‖ ^ 2) ((2 : ℝ) • innerCLM E x) x := by sorry
