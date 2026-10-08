-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_inv_smul_section
-- name    : BookProof.ChapterMackeyImprimitivity.inv_smul_section
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T14:00:32.691995+00:00
-- url     : https://prove2.me/theorems/9a33a8da-e078-4e10-aa9b-97f2f108b364
-- title:
--   `BookProof.ChapterMackeyImprimitivity.inv_smul_section` (hs : ∀ x, s x • x₀ = x) (x : X) : (s x)⁻¹ • x = x₀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.inv_smul_section` (hs : ∀ x, s x • x₀ = x) (x : X) : (s x)⁻¹ • x = x₀
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.inv_smul_section`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.inv_smul_section
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : ImprimitivitySystem G X E)
variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem BookProof.ChapterMackeyImprimitivity.inv_smul_section (hs : ∀ x, s x • x₀ = x) (x : X) : (s x)⁻¹ • x = x₀ := by sorry
