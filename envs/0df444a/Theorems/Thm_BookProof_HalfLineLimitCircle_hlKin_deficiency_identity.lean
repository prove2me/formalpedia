-- Prove2me | Theorems.Thm_BookProof_HalfLineLimitCircle_hlKin_deficiency_identity
-- name    : BookProof.HalfLineLimitCircle.hlKin_deficiency_identity
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:56:45.338057+00:00
-- url     : https://prove2.me/theorems/0f805f43-b3bb-4a81-989b-2c6dcb02a1f2
-- title:
--   `BookProof.HalfLineLimitCircle.hlKin_deficiency_identity` (v : hlCore) : (inner ℂ (hlKin v) deficiencyVec : ℂ) = Complex.I * inner ℂ (v : HL) deficiencyVec
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHalfLineLimitCircle`.
--
--   `BookProof.HalfLineLimitCircle.hlKin_deficiency_identity` (v : hlCore) : (inner ℂ (hlKin v) deficiencyVec : ℂ) = Complex.I * inner ℂ (v : HL) deficiencyVec
--
--   Formalization note: Lean 4 identifier `BookProof.HalfLineLimitCircle.hlKin_deficiency_identity`.

-- Generated from ChapterHalfLineLimitCircle.lean — theorem BookProof.HalfLineLimitCircle.hlKin_deficiency_identity
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
open BookProof.HalfLineLimitCircle



open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem BookProof.HalfLineLimitCircle.hlKin_deficiency_identity (v : hlCore) :
    (inner ℂ (hlKin v) deficiencyVec : ℂ) = Complex.I * inner ℂ (v : HL) deficiencyVec := by sorry
