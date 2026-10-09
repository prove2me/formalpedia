-- Prove2me | Theorems.Thm_BookProof_HalfLineLimitCircle_hlKin_apply
-- name    : BookProof.HalfLineLimitCircle.hlKin_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:56:46.366981+00:00
-- url     : https://prove2.me/theorems/1c3df871-dbf1-4d30-b161-00d7986cd862
-- title:
--   `BookProof.HalfLineLimitCircle.hlKin_apply` (f : testSpace) : hlKin (hlEquiv f) = -testIncl (deriv2LM f)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHalfLineLimitCircle`.
--
--   `BookProof.HalfLineLimitCircle.hlKin_apply` (f : testSpace) : hlKin (hlEquiv f) = -testIncl (deriv2LM f)
--
--   Formalization note: Lean 4 identifier `BookProof.HalfLineLimitCircle.hlKin_apply`.

-- Generated from ChapterHalfLineLimitCircle.lean — theorem BookProof.HalfLineLimitCircle.hlKin_apply
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
open BookProof.HalfLineLimitCircle



open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem BookProof.HalfLineLimitCircle.hlKin_apply (f : testSpace) : hlKin (hlEquiv f) = -testIncl (deriv2LM f) := by sorry
