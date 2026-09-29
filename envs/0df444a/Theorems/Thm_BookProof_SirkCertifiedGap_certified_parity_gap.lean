-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_certified_parity_gap
-- name    : BookProof.SirkCertifiedGap.certified_parity_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:01:38.88606+00:00
-- url     : https://prove2.me/theorems/3485bd3a-bf8f-44c1-9848-7e3274ed8f9e
-- title:
--   {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ} (hEven : sectorGround T P 1 ≤ thetaE + deltaE) (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) : thetaO - thetaE - (deltaO + deltaE) ≤...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.certified_parity_gap` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certified_parity_gap
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.certified_parity_gap {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ}
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) :
    thetaO - thetaE - (deltaO + deltaE) ≤ sectorGround T P (-1) - sectorGround T P 1 := by sorry
