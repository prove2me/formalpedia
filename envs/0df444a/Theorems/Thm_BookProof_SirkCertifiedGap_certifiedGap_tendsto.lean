-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_certifiedGap_tendsto
-- name    : BookProof.SirkCertifiedGap.certifiedGap_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:00:59.547269+00:00
-- url     : https://prove2.me/theorems/4499291a-fcd8-4c29-bde9-373ba1d4f1c6
-- title:
--   {thetaE thetaO deltaE deltaO : ℕ → ℝ} {lamE lamO : ℝ} (hE : Tendsto thetaE atTop (𝓝 lamE)) (hO : Tendsto thetaO atTop (𝓝 lamO)) (hdE : Tendsto deltaE atTop (𝓝 0)) (hdO : Tendsto deltaO atTop (𝓝...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.certifiedGap_tendsto` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certifiedGap_tendsto
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.certifiedGap_tendsto {thetaE thetaO deltaE deltaO : ℕ → ℝ} {lamE lamO : ℝ}
    (hE : Tendsto thetaE atTop (𝓝 lamE)) (hO : Tendsto thetaO atTop (𝓝 lamO))
    (hdE : Tendsto deltaE atTop (𝓝 0)) (hdO : Tendsto deltaO atTop (𝓝 0)) :
    Tendsto (certifiedGap thetaE thetaO deltaE deltaO) atTop (𝓝 (lamO - lamE)) := by sorry
