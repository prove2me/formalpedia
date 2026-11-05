-- Prove2me | Theorems.Thm_BookProof_NonnegResolvent_tendsto_smul_resAt
-- name    : BookProof.NonnegResolvent.tendsto_smul_resAt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T22:53:16.126891+00:00
-- url     : https://prove2.me/theorems/3705d22d-9f4d-43c7-a180-c6fc15499959
-- title:
--   `BookProof.NonnegResolvent.tendsto_smul_resAt` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (h : F) : Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNonnegResolvent`.
--
--   `BookProof.NonnegResolvent.tendsto_smul_resAt` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (h : F) : Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) • resAt hT n h) Filter.atTop (nhds h)
--
--   Formalization note: Lean 4 identifier `BookProof.NonnegResolvent.tendsto_smul_resAt`.

-- Generated from ChapterNonnegResolvent.lean — theorem BookProof.NonnegResolvent.tendsto_smul_resAt
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegSquareRoot
import Mathlib
import Definitions.Def_ChapterNonnegResolvent



open BookProof.ClosureUniqueness
open scoped ComplexOrder
open BookProof.PositiveSquareRoot

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T : Submodule ℂ (F × F)} {a b : ℝ}

theorem BookProof.NonnegResolvent.tendsto_smul_resAt (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (h : F) :
    Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) • resAt hT n h) Filter.atTop
      (nhds h) := by sorry
