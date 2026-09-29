-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_certified_parity_gap_pos
-- name    : BookProof.SirkCertifiedGap.certified_parity_gap_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:27:53.568098+00:00
-- url     : https://prove2.me/theorems/12d5b3a7-6012-42e1-b2d8-e3a58faa050c
-- title:
--   {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ} (hEven : sectorGround T P 1 ≤ thetaE + deltaE) (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) (hsep : 0 < thetaO - thetaE - (deltaO +...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.certified_parity_gap_pos` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certified_parity_gap_pos
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.certified_parity_gap_pos {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ}
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1))
    (hsep : 0 < thetaO - thetaE - (deltaO + deltaE)) :
    sectorGround T P 1 < sectorGround T P (-1) := by sorry
