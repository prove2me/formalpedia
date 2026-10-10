-- Prove2me | Theorems.Thm_BookProof_HalfLineLimitCircle_inner_eq_integral
-- name    : BookProof.HalfLineLimitCircle.inner_eq_integral
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:57:55.139269+00:00
-- url     : https://prove2.me/theorems/b35579b7-5107-4891-9974-d3653f5cd3b6
-- title:
--   `BookProof.HalfLineLimitCircle.inner_eq_integral` {u v : HL} {a b : ℝ → ℂ} (hu : (u : ℝ → ℂ) =ᵐ[hlMeasure] a) (hv : (v : ℝ → ℂ) =ᵐ[hlMeasure] b) : (inner ℂ u v : ℂ) =...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHalfLineLimitCircle`.
--
--   `BookProof.HalfLineLimitCircle.inner_eq_integral` {u v : HL} {a b : ℝ → ℂ} (hu : (u : ℝ → ℂ) =ᵐ[hlMeasure] a) (hv : (v : ℝ → ℂ) =ᵐ[hlMeasure] b) : (inner ℂ u v : ℂ) = ∫ x in Ioi (0:ℝ), (starRingEnd ℂ) (a x) * b x
--
--   Formalization note: Lean 4 identifier `BookProof.HalfLineLimitCircle.inner_eq_integral`.

-- Generated from ChapterHalfLineLimitCircle.lean — theorem BookProof.HalfLineLimitCircle.inner_eq_integral
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
open BookProof.HalfLineLimitCircle



open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem BookProof.HalfLineLimitCircle.inner_eq_integral {u v : HL} {a b : ℝ → ℂ}
    (hu : (u : ℝ → ℂ) =ᵐ[hlMeasure] a) (hv : (v : ℝ → ℂ) =ᵐ[hlMeasure] b) :
    (inner ℂ u v : ℂ) = ∫ x in Ioi (0:ℝ), (starRingEnd ℂ) (a x) * b x := by sorry
