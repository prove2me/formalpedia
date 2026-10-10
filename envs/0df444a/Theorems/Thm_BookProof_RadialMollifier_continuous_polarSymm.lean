-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_continuous_polarSymm
-- name    : BookProof.RadialMollifier.continuous_polarSymm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:01:49.660971+00:00
-- url     : https://prove2.me/theorems/c85f7b85-ab06-4b80-ab18-84aecf53cf32
-- title:
--   `BookProof.RadialMollifier.continuous_polarSymm` : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.continuous_polarSymm` : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.continuous_polarSymm`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.continuous_polarSymm
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.continuous_polarSymm : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by sorry
