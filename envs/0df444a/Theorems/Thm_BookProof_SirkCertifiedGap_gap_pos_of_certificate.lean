-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_gap_pos_of_certificate
-- name    : BookProof.SirkCertifiedGap.gap_pos_of_certificate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:35:11.655438+00:00
-- url     : https://prove2.me/theorems/3234c862-749d-4a45-a2f7-fa862a8add03
-- title:
--   {T P : E →ₗ[ℂ] E} (c : GapCertificate) {thetaE thetaO deltaE deltaO : ℝ} (hgap : c.gap = thetaO - thetaE) (hwidth : c.width = deltaO + deltaE) (hEven : sectorGround T P 1 ≤ thetaE + deltaE) (hOdd...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.gap_pos_of_certificate` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.gap_pos_of_certificate
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.gap_pos_of_certificate {T P : E →ₗ[ℂ] E} (c : GapCertificate)
    {thetaE thetaO deltaE deltaO : ℝ}
    (hgap : c.gap = thetaO - thetaE) (hwidth : c.width = deltaO + deltaE)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1))
    (hpos : 0 < c.lower) :
    sectorGround T P 1 < sectorGround T P (-1) := by sorry
