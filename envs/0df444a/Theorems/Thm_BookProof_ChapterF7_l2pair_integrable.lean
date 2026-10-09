-- Prove2me | Theorems.Thm_BookProof_ChapterF7_l2pair_integrable
-- name    : BookProof.ChapterF7.l2pair_integrable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:04:28.388991+00:00
-- url     : https://prove2.me/theorems/4d22eff6-5b56-433c-b326-fb145851210f
-- title:
--   `BookProof.ChapterF7.l2pair_integrable` (f g : 𝓢(ℝ, ℂ)) : Integrable (fun x => (starRingEnd ℂ) (f x) * g x) volume
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.l2pair_integrable` (f g : 𝓢(ℝ, ℂ)) : Integrable (fun x => (starRingEnd ℂ) (f x) * g x) volume
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.l2pair_integrable`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.l2pair_integrable
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.l2pair_integrable (f g : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => (starRingEnd ℂ) (f x) * g x) volume := by sorry
