-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_moll_polarSymm
-- name    : BookProof.RadialMollifier.moll_polarSymm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:02:46.267535+00:00
-- url     : https://prove2.me/theorems/93f5a06c-f1cb-497a-945a-0d824915ec4d
-- title:
--   `BookProof.RadialMollifier.moll_polarSymm` {δ r θ : ℝ} (hr : 0 < r) : moll δ (Complex.polarCoord.symm (r, θ)) = moll δ (r : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.moll_polarSymm` {δ r θ : ℝ} (hr : 0 < r) : moll δ (Complex.polarCoord.symm (r, θ)) = moll δ (r : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.moll_polarSymm`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.moll_polarSymm
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.moll_polarSymm {δ r θ : ℝ} (hr : 0 < r) :
    moll δ (Complex.polarCoord.symm (r, θ)) = moll δ (r : ℂ) := by sorry
