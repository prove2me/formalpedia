-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_dist_synthesis_retained_le
-- name    : BookProof.ChapterSirkGramCutoff.dist_synthesis_retained_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:05:11.684029+00:00
-- url     : https://prove2.me/theorems/f169e978-3673-43be-9665-52762da15b32
-- title:
--   (heig : IsGramEigen w u lam) {tol : ℝ} (R : Finset (Fin m)) (hcut : ∀ k ∉ R, lam k ≤ tol) (c : EuclideanSpace ℂ (Fin m)) : ‖synthesis w c - ∑ k ∈ R, ⟪u k, c⟫_ℂ • synthesis...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.dist_synthesis_retained_le` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.dist_synthesis_retained_le
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
open BookProof.ChapterSirkGramCutoff









noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

theorem BookProof.ChapterSirkGramCutoff.dist_synthesis_retained_le (heig : IsGramEigen w u lam) {tol : ℝ}
    (R : Finset (Fin m)) (hcut : ∀ k ∉ R, lam k ≤ tol) (c : EuclideanSpace ℂ (Fin m)) :
    ‖synthesis w c - ∑ k ∈ R, ⟪u k, c⟫_ℂ • synthesis w (u k)‖ ≤ Real.sqrt tol * ‖c‖ := by sorry
