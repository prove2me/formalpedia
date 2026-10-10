-- Prove2me | Theorems.Thm_BookProof_HalfLineLimitCircle_setIntegral_eq_integral_of_testSpace
-- name    : BookProof.HalfLineLimitCircle.setIntegral_eq_integral_of_testSpace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:55:23.931985+00:00
-- url     : https://prove2.me/theorems/5d05ab9c-2a98-4c1b-bd38-8f7a575cd8c0
-- title:
--   `BookProof.HalfLineLimitCircle.setIntegral_eq_integral_of_testSpace` {f : ℝ → ℂ} (hf : f ∈ testSpace) (w : ℝ → ℂ) : ∫ x in Ioi (0 : ℝ), (starRingEnd ℂ) (f x) * w x = ∫ x,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHalfLineLimitCircle`.
--
--   `BookProof.HalfLineLimitCircle.setIntegral_eq_integral_of_testSpace` {f : ℝ → ℂ} (hf : f ∈ testSpace) (w : ℝ → ℂ) : ∫ x in Ioi (0 : ℝ), (starRingEnd ℂ) (f x) * w x = ∫ x, (starRingEnd ℂ) (f x) * w x
--
--   Formalization note: Lean 4 identifier `BookProof.HalfLineLimitCircle.setIntegral_eq_integral_of_testSpace`.

-- Generated from ChapterHalfLineLimitCircle.lean — theorem BookProof.HalfLineLimitCircle.setIntegral_eq_integral_of_testSpace
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
open BookProof.HalfLineLimitCircle



open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem BookProof.HalfLineLimitCircle.setIntegral_eq_integral_of_testSpace {f : ℝ → ℂ} (hf : f ∈ testSpace) (w : ℝ → ℂ) :
    ∫ x in Ioi (0 : ℝ), (starRingEnd ℂ) (f x) * w x = ∫ x, (starRingEnd ℂ) (f x) * w x := by sorry
