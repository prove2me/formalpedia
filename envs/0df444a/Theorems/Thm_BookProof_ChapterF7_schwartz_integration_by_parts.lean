-- Prove2me | Theorems.Thm_BookProof_ChapterF7_schwartz_integration_by_parts
-- name    : BookProof.ChapterF7.schwartz_integration_by_parts
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:06:48.508229+00:00
-- url     : https://prove2.me/theorems/650db25a-f57c-4587-b729-829636aad077
-- title:
--   `BookProof.ChapterF7.schwartz_integration_by_parts` (f g : 𝓢(ℝ, ℂ)) : (∫ x, (starRingEnd ℂ) (deriv (f : ℝ → ℂ) x) * g x) = - ∫ x, (starRingEnd ℂ) (f x) * deriv (g : ℝ → ℂ) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.schwartz_integration_by_parts` (f g : 𝓢(ℝ, ℂ)) : (∫ x, (starRingEnd ℂ) (deriv (f : ℝ → ℂ) x) * g x) = - ∫ x, (starRingEnd ℂ) (f x) * deriv (g : ℝ → ℂ) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.schwartz_integration_by_parts`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.schwartz_integration_by_parts
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.schwartz_integration_by_parts (f g : 𝓢(ℝ, ℂ)) :
    (∫ x, (starRingEnd ℂ) (deriv (f : ℝ → ℂ) x) * g x)
      = - ∫ x, (starRingEnd ℂ) (f x) * deriv (g : ℝ → ℂ) x := by sorry
