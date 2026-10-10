-- Prove2me | Theorems.Thm_BookProof_ChapterLpRestrictSplit_restrictEmbed_restrictProj_coeFn
-- name    : BookProof.ChapterLpRestrictSplit.restrictEmbed_restrictProj_coeFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:47:00.070295+00:00
-- url     : https://prove2.me/theorems/8562d97e-12da-4be2-be0f-ad87a08e94e1
-- title:
--   `BookProof.ChapterLpRestrictSplit.restrictEmbed_restrictProj_coeFn` {A : Set α} (hA : MeasurableSet A) (u : Lp ℂ 2 mu) : (restrictEmbed hA (restrictProj A u) : α → ℂ) =ᵐ[mu] A.indi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLpRestrictSplit`.
--
--   `BookProof.ChapterLpRestrictSplit.restrictEmbed_restrictProj_coeFn` {A : Set α} (hA : MeasurableSet A) (u : Lp ℂ 2 mu) : (restrictEmbed hA (restrictProj A u) : α → ℂ) =ᵐ[mu] A.indicator (u : α → ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLpRestrictSplit.restrictEmbed_restrictProj_coeFn`.

-- Generated from ChapterLpRestrictSplit.lean — theorem BookProof.ChapterLpRestrictSplit.restrictEmbed_restrictProj_coeFn
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLpRestrictSplit
open BookProof.ChapterLpRestrictSplit


noncomputable section

open MeasureTheory


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

theorem BookProof.ChapterLpRestrictSplit.restrictEmbed_restrictProj_coeFn {A : Set α} (hA : MeasurableSet A) (u : Lp ℂ 2 mu) :
    (restrictEmbed hA (restrictProj A u) : α → ℂ) =ᵐ[mu] A.indicator (u : α → ℂ) := by sorry
