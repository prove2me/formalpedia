-- Prove2me | Theorems.Thm_BookProof_ChapterBornMeasure_lintegral_bornDensity
-- name    : BookProof.ChapterBornMeasure.lintegral_bornDensity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:57:01.275451+00:00
-- url     : https://prove2.me/theorems/2591c5e7-f9a8-4efc-8d02-8a945e807e51
-- title:
--   `BookProof.ChapterBornMeasure.lintegral_bornDensity` (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) : ∫⁻ x, ‖(psi : α → ℂ) x‖ₑ ^ 2 ∂μ = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBornMeasure`.
--
--   `BookProof.ChapterBornMeasure.lintegral_bornDensity` (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) : ∫⁻ x, ‖(psi : α → ℂ) x‖ₑ ^ 2 ∂μ = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBornMeasure.lintegral_bornDensity`.

-- Generated from ChapterBornMeasure.lean — theorem BookProof.ChapterBornMeasure.lintegral_bornDensity
import Mathlib
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure


open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterBornMeasure.lintegral_bornDensity (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) :
    ∫⁻ x, ‖(psi : α → ℂ) x‖ₑ ^ 2 ∂μ = 1 := by sorry
