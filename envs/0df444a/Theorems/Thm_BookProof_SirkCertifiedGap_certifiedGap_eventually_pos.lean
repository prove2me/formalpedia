-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_certifiedGap_eventually_pos
-- name    : BookProof.SirkCertifiedGap.certifiedGap_eventually_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:27:11.974108+00:00
-- url     : https://prove2.me/theorems/9cfafd67-614d-499d-99fc-5e928cd146a0
-- title:
--   {thetaE thetaO deltaE deltaO : ℕ → ℝ} {lamE lamO : ℝ} (hE : Tendsto thetaE atTop (𝓝 lamE)) (hO : Tendsto thetaO atTop (𝓝 lamO)) (hdE : Tendsto deltaE atTop (𝓝 0)) (hdO : Tendsto deltaO atTop (𝓝...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.certifiedGap_eventually_pos` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certifiedGap_eventually_pos
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.certifiedGap_eventually_pos {thetaE thetaO deltaE deltaO : ℕ → ℝ} {lamE lamO : ℝ}
    (hE : Tendsto thetaE atTop (𝓝 lamE)) (hO : Tendsto thetaO atTop (𝓝 lamO))
    (hdE : Tendsto deltaE atTop (𝓝 0)) (hdO : Tendsto deltaO atTop (𝓝 0))
    (hmu : 0 < lamO - lamE) :
    ∃ m0 : ℕ, ∀ m ≥ m0, 0 < certifiedGap thetaE thetaO deltaE deltaO m := by sorry
