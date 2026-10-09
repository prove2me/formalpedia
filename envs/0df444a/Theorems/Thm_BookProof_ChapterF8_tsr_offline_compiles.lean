-- Prove2me | Theorems.Thm_BookProof_ChapterF8_tsr_offline_compiles
-- name    : BookProof.ChapterF8.tsr_offline_compiles
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:09:17.641843+00:00
-- url     : https://prove2.me/theorems/4bf8360f-0aae-4af8-897d-850ade581354
-- title:
--   `BookProof.ChapterF8.tsr_offline_compiles` {d k K₂ m : ℕ} (h : Fin d → Fin k) (g : Fin k → Fin K₂) (hg : Function.Injective g) : (∀ x : Fin d → ℝ, twoLevelHash h g x ∈ singleExcita
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF8`.
--
--   `BookProof.ChapterF8.tsr_offline_compiles` {d k K₂ m : ℕ} (h : Fin d → Fin k) (g : Fin k → Fin K₂) (hg : Function.Injective g) : (∀ x : Fin d → ℝ, twoLevelHash h g x ∈ singleExcitation K₂) ∧ (∀ (x : Fin d → ℝ) (j : Fin k), twoLevelHash h g x (Finsupp.single (g j) 1) = ((featureHash h x j : ℝ) : ℂ)) ∧ Submodule.span ℂ (operatorBasis m) = ⊤ ∧ (∀ M M' : ℕ, totalCost M d m K₂ k + offlineCost M' d k = totalCost M' d m K₂ k + offlineCost M d k)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF8.tsr_offline_compiles`.

-- Generated from ChapterF8.lean — theorem BookProof.ChapterF8.tsr_offline_compiles
import Mathlib
import Definitions.Def_ChapterF8
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow.FockManyMode
open BookProof.ChapterF8


noncomputable section

open scoped BigOperators

theorem BookProof.ChapterF8.tsr_offline_compiles {d k K₂ m : ℕ} (h : Fin d → Fin k) (g : Fin k → Fin K₂)
    (hg : Function.Injective g) :
    (∀ x : Fin d → ℝ, twoLevelHash h g x ∈ singleExcitation K₂) ∧
    (∀ (x : Fin d → ℝ) (j : Fin k),
      twoLevelHash h g x (Finsupp.single (g j) 1) = ((featureHash h x j : ℝ) : ℂ)) ∧
    Submodule.span ℂ (operatorBasis m) = ⊤ ∧
    (∀ M M' : ℕ, totalCost M d m K₂ k + offlineCost M' d k
      = totalCost M' d m K₂ k + offlineCost M d k) := by sorry
