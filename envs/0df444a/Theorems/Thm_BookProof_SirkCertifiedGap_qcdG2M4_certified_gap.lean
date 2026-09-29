-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_qcdG2M4_certified_gap
-- name    : BookProof.SirkCertifiedGap.qcdG2M4_certified_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:35:07.633815+00:00
-- url     : https://prove2.me/theorems/dc9513d4-18ea-449c-bacc-ce130e112885
-- title:
--   {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ} (hgap : thetaO - thetaE = 1.9875) (hwidth : deltaO + deltaE = 0.0555) (hEven : sectorGround T P 1 ≤ thetaE + deltaE) (hOdd : thetaO - deltaO ≤...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.qcdG2M4_certified_gap` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.qcdG2M4_certified_gap
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.qcdG2M4_certified_gap {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ}
    (hgap : thetaO - thetaE = 1.9875) (hwidth : deltaO + deltaE = 0.0555)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) :
    (1.932 : ℝ) ≤ sectorGround T P (-1) - sectorGround T P 1
      ∧ sectorGround T P 1 < sectorGround T P (-1) := by sorry
