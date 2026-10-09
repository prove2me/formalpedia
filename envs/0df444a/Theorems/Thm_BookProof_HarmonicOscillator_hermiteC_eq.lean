-- Prove2me | Theorems.Thm_BookProof_HarmonicOscillator_hermiteC_eq
-- name    : BookProof.HarmonicOscillator.hermiteC_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:58:40.088434+00:00
-- url     : https://prove2.me/theorems/494eb19f-c4da-470e-8872-e3efe2970156
-- title:
--   `BookProof.HarmonicOscillator.hermiteC_eq` (n : ℕ) : hermiteC n = fun x => ((hermiteNorm n : ℝ) : ℂ)⁻¹ * polyGaussC (hermiteR n) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHarmonicOscillatorEsa`.
--
--   `BookProof.HarmonicOscillator.hermiteC_eq` (n : ℕ) : hermiteC n = fun x => ((hermiteNorm n : ℝ) : ℂ)⁻¹ * polyGaussC (hermiteR n) x
--
--   Formalization note: Lean 4 identifier `BookProof.HarmonicOscillator.hermiteC_eq`.

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.hermiteC_eq
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

theorem BookProof.HarmonicOscillator.hermiteC_eq (n : ℕ) :
    hermiteC n = fun x => ((hermiteNorm n : ℝ) : ℂ)⁻¹ * polyGaussC (hermiteR n) x := by sorry
