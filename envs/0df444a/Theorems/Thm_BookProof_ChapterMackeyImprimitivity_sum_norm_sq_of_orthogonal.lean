-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_sum_norm_sq_of_orthogonal
-- name    : BookProof.ChapterMackeyImprimitivity.sum_norm_sq_of_orthogonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:49:03.364997+00:00
-- url     : https://prove2.me/theorems/c4cd5b25-7eb1-4ec8-b3b5-a67682ff81b2
-- title:
--   `BookProof.ChapterMackeyImprimitivity.sum_norm_sq_of_orthogonal` {f : X → E} {ψ : E} (hsum : ∑ x, f x = ψ) (horth : ∀ x y, x ≠ y → ⟪f x, f y⟫_ℂ = 0) : ∑ x : X, ‖f x‖ ^ 2...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.sum_norm_sq_of_orthogonal` {f : X → E} {ψ : E} (hsum : ∑ x, f x = ψ) (horth : ∀ x y, x ≠ y → ⟪f x, f y⟫_ℂ = 0) : ∑ x : X, ‖f x‖ ^ 2 = ‖ψ‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.sum_norm_sq_of_orthogonal`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.sum_norm_sq_of_orthogonal
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterMackeyImprimitivity.sum_norm_sq_of_orthogonal {f : X → E} {ψ : E} (hsum : ∑ x, f x = ψ)
    (horth : ∀ x y, x ≠ y → ⟪f x, f y⟫_ℂ = 0) :
    ∑ x : X, ‖f x‖ ^ 2 = ‖ψ‖ ^ 2 := by sorry
