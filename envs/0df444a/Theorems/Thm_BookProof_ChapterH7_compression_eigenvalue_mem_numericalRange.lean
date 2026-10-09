-- Prove2me | Theorems.Thm_BookProof_ChapterH7_compression_eigenvalue_mem_numericalRange
-- name    : BookProof.ChapterH7.compression_eigenvalue_mem_numericalRange
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:53:44.775828+00:00
-- url     : https://prove2.me/theorems/2a7cbc73-f0cb-4c12-a743-481eda6da584
-- title:
--   `BookProof.ChapterH7.compression_eigenvalue_mem_numericalRange` (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) {lam : ℂ} {y : F} (hy :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH7`.
--
--   `BookProof.ChapterH7.compression_eigenvalue_mem_numericalRange` (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) {lam : ℂ} {y : F} (hy : ‖y‖ = 1) (heig : compress V X y = lam • y) {a b : ℝ} (hlow : ∀ x : E, ‖x‖ = 1 → a ≤ (inner ℂ x (X x) : ℂ).re) (hhigh : ∀ x : E, ‖x‖ = 1 → (inner ℂ x (X x) : ℂ).re ≤ b) : lam.im = 0 ∧ a ≤ lam.re ∧ lam.re ≤ b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH7.compression_eigenvalue_mem_numericalRange`.

-- Generated from ChapterH7.lean — theorem BookProof.ChapterH7.compression_eigenvalue_mem_numericalRange
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterH4
open BookProof.ChapterH4
open BookProof.ChapterH7


noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterH7.compression_eigenvalue_mem_numericalRange (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hX : IsSelfAdjoint X) (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    {lam : ℂ} {y : F} (hy : ‖y‖ = 1) (heig : compress V X y = lam • y)
    {a b : ℝ} (hlow : ∀ x : E, ‖x‖ = 1 → a ≤ (inner ℂ x (X x) : ℂ).re)
    (hhigh : ∀ x : E, ‖x‖ = 1 → (inner ℂ x (X x) : ℂ).re ≤ b) :
    lam.im = 0 ∧ a ≤ lam.re ∧ lam.re ≤ b := by sorry
