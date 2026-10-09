-- Prove2me | Theorems.Thm_BookProof_HalfLineLimitCircle_hasCompactSupport_conj
-- name    : BookProof.HalfLineLimitCircle.hasCompactSupport_conj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:54:59.172821+00:00
-- url     : https://prove2.me/theorems/42c4dac5-98c7-431f-83a5-2d4dbc1c01ef
-- title:
--   `BookProof.HalfLineLimitCircle.hasCompactSupport_conj` {f : ℝ → ℂ} (hf : HasCompactSupport f) : HasCompactSupport fun x => (starRingEnd ℂ) (f x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHalfLineLimitCircle`.
--
--   `BookProof.HalfLineLimitCircle.hasCompactSupport_conj` {f : ℝ → ℂ} (hf : HasCompactSupport f) : HasCompactSupport fun x => (starRingEnd ℂ) (f x)
--
--   Formalization note: Lean 4 identifier `BookProof.HalfLineLimitCircle.hasCompactSupport_conj`.

-- Generated from ChapterHalfLineLimitCircle.lean — theorem BookProof.HalfLineLimitCircle.hasCompactSupport_conj
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
open BookProof.HalfLineLimitCircle



open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem BookProof.HalfLineLimitCircle.hasCompactSupport_conj {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport fun x => (starRingEnd ℂ) (f x) := by sorry
