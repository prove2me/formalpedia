-- Prove2me | Theorems.Thm_BookProof_ChapterHilbertSumIntertwine_memLp_fibrewise
-- name    : BookProof.ChapterHilbertSumIntertwine.memLp_fibrewise
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T08:25:32.916352+00:00
-- url     : https://prove2.me/theorems/48880e84-89e2-4ec1-bb96-1be25cf6d02c
-- title:
--   `BookProof.ChapterHilbertSumIntertwine.memLp_fibrewise` (B : ∀ i, G i →L[ℂ] G i) (hB : ∀ i u, ‖B i u‖ ≤ ‖u‖) (w : lp G 2) : Memℓp (fun i => B i (w i)) 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHilbertSumIntertwine`.
--
--   `BookProof.ChapterHilbertSumIntertwine.memLp_fibrewise` (B : ∀ i, G i →L[ℂ] G i) (hB : ∀ i u, ‖B i u‖ ≤ ‖u‖) (w : lp G 2) : Memℓp (fun i => B i (w i)) 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHilbertSumIntertwine.memLp_fibrewise`.

-- Generated from ChapterHilbertSumIntertwine.lean — theorem BookProof.ChapterHilbertSumIntertwine.memℓp_fibrewise
import Mathlib
import Definitions.Def_ChapterHilbertSumIntertwine
open BookProof.ChapterHilbertSumIntertwine


open scoped InnerProductSpace



variable {ι : Type*}
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]

theorem BookProof.ChapterHilbertSumIntertwine.memLp_fibrewise (B : ∀ i, G i →L[ℂ] G i) (hB : ∀ i u, ‖B i u‖ ≤ ‖u‖)
    (w : lp G 2) : Memℓp (fun i => B i (w i)) 2 := by sorry
