-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_normSqPow
-- name    : BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:56:08.039992+00:00
-- url     : https://prove2.me/theorems/5fdea519-342e-4910-a977-c16f87db3e58
-- title:
--   `BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow` (m : ℕ) (x : E) : (Δ fun y : E => (‖y‖ ^ 2) ^ m) x = (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m) * (‖x‖ ^ 2) ^
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow` (m : ℕ) (x : E) : (Δ fun y : E => (‖y‖ ^ 2) ^ m) x = (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m) * (‖x‖ ^ 2) ^ (m - 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow (m : ℕ) (x : E) :
    (Δ fun y : E => (‖y‖ ^ 2) ^ m) x
      = (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m) * (‖x‖ ^ 2) ^ (m - 1) := by sorry
