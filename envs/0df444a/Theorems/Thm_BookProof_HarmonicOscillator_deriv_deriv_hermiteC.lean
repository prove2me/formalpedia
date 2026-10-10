-- Prove2me | Theorems.Thm_BookProof_HarmonicOscillator_deriv_deriv_hermiteC
-- name    : BookProof.HarmonicOscillator.deriv_deriv_hermiteC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:59:10.917581+00:00
-- url     : https://prove2.me/theorems/2d5cb50d-6e3d-46aa-9c40-e725d5830da2
-- title:
--   `BookProof.HarmonicOscillator.deriv_deriv_hermiteC` (n : ℕ) (x : ℝ) : deriv (deriv (hermiteC n)) x = ((hermiteNorm n : ℝ) : ℂ)⁻¹ * ((deriv (deriv (hermiteFun n)) x : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHarmonicOscillatorEsa`.
--
--   `BookProof.HarmonicOscillator.deriv_deriv_hermiteC` (n : ℕ) (x : ℝ) : deriv (deriv (hermiteC n)) x = ((hermiteNorm n : ℝ) : ℂ)⁻¹ * ((deriv (deriv (hermiteFun n)) x : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.HarmonicOscillator.deriv_deriv_hermiteC`.

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.deriv_deriv_hermiteC
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

theorem BookProof.HarmonicOscillator.deriv_deriv_hermiteC (n : ℕ) (x : ℝ) :
    deriv (deriv (hermiteC n)) x
      = ((hermiteNorm n : ℝ) : ℂ)⁻¹ * ((deriv (deriv (hermiteFun n)) x : ℝ) : ℂ) := by sorry
