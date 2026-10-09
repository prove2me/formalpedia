-- Prove2me | Theorems.Thm_BookProof_HarmonicOscillator_deriv_const_mul_fun
-- name    : BookProof.HarmonicOscillator.deriv_const_mul_fun
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:58:41.700244+00:00
-- url     : https://prove2.me/theorems/b50d99a2-4ab0-4d88-9866-86da7430229a
-- title:
--   `BookProof.HarmonicOscillator.deriv_const_mul_fun` (c : ℂ) {f : ℝ → ℂ} (hf : ∀ x, DifferentiableAt ℝ f x) : deriv (fun x => c * f x) = fun x => c * deriv f x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHarmonicOscillatorEsa`.
--
--   `BookProof.HarmonicOscillator.deriv_const_mul_fun` (c : ℂ) {f : ℝ → ℂ} (hf : ∀ x, DifferentiableAt ℝ f x) : deriv (fun x => c * f x) = fun x => c * deriv f x
--
--   Formalization note: Lean 4 identifier `BookProof.HarmonicOscillator.deriv_const_mul_fun`.

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.deriv_const_mul_fun
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

theorem BookProof.HarmonicOscillator.deriv_const_mul_fun (c : ℂ) {f : ℝ → ℂ} (hf : ∀ x, DifferentiableAt ℝ f x) :
    deriv (fun x => c * f x) = fun x => c * deriv f x := by sorry
