-- Prove2me | Theorems.Thm_BookProof_ChapterHilbertSumIntertwine_linearIsometryEquiv_intertwine
-- name    : BookProof.ChapterHilbertSumIntertwine.linearIsometryEquiv_intertwine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T10:17:12.501518+00:00
-- url     : https://prove2.me/theorems/bea05fa5-e3a3-4145-9698-b46cb125faaa
-- title:
--   `BookProof.ChapterHilbertSumIntertwine.linearIsometryEquiv_intertwine` {V : ∀ i, G i →ₗᵢ[ℂ] H} (hsum : IsHilbertSum ℂ G V) (A : H →L[ℂ] H) (B : ∀ i, G i →L[ℂ] G i) (hB : ∀...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHilbertSumIntertwine`.
--
--   `BookProof.ChapterHilbertSumIntertwine.linearIsometryEquiv_intertwine` {V : ∀ i, G i →ₗᵢ[ℂ] H} (hsum : IsHilbertSum ℂ G V) (A : H →L[ℂ] H) (B : ∀ i, G i →L[ℂ] G i) (hB : ∀ i u, ‖B i u‖ ≤ ‖u‖) (hcomm : ∀ i u, V i (B i u) = A (V i u)) (v : H) (i : ι) : hsum.linearIsometryEquiv (A v) i = B i (hsum.linearIsometryEquiv v i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHilbertSumIntertwine.linearIsometryEquiv_intertwine`.

-- Generated from ChapterHilbertSumIntertwine.lean — theorem BookProof.ChapterHilbertSumIntertwine.linearIsometryEquiv_intertwine
import Mathlib
import Definitions.Def_ChapterHilbertSumIntertwine
open BookProof.ChapterHilbertSumIntertwine


open scoped InnerProductSpace



variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]

theorem BookProof.ChapterHilbertSumIntertwine.linearIsometryEquiv_intertwine {V : ∀ i, G i →ₗᵢ[ℂ] H} (hsum : IsHilbertSum ℂ G V)
    (A : H →L[ℂ] H) (B : ∀ i, G i →L[ℂ] G i) (hB : ∀ i u, ‖B i u‖ ≤ ‖u‖)
    (hcomm : ∀ i u, V i (B i u) = A (V i u)) (v : H) (i : ι) :
    hsum.linearIsometryEquiv (A v) i = B i (hsum.linearIsometryEquiv v i) := by sorry
