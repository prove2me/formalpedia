-- Prove2me | Theorems.Thm_BookProof_HalfLineLimitCircle_hlKin_neg_not_essentiallySelfAdjointOn
-- name    : BookProof.HalfLineLimitCircle.hlKin_neg_not_essentiallySelfAdjointOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:57:09.817928+00:00
-- url     : https://prove2.me/theorems/3da59795-7b11-41c3-a392-497a61ac2f60
-- title:
--   `BookProof.HalfLineLimitCircle.hlKin_neg_not_essentiallySelfAdjointOn` : ¬ EssentiallySelfAdjointOn hlCore (-hlKin)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHalfLineLimitCircle`.
--
--   `BookProof.HalfLineLimitCircle.hlKin_neg_not_essentiallySelfAdjointOn` : ¬ EssentiallySelfAdjointOn hlCore (-hlKin)
--
--   Formalization note: Lean 4 identifier `BookProof.HalfLineLimitCircle.hlKin_neg_not_essentiallySelfAdjointOn`.

-- Generated from ChapterHalfLineLimitCircle.lean — theorem BookProof.HalfLineLimitCircle.hlKin_neg_not_essentiallySelfAdjointOn
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HalfLineLimitCircle



open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem BookProof.HalfLineLimitCircle.hlKin_neg_not_essentiallySelfAdjointOn : ¬ EssentiallySelfAdjointOn hlCore (-hlKin) := by sorry
