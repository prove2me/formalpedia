-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_certified_parity_gap_strong_coupling
-- name    : BookProof.SirkCertifiedGap.certified_parity_gap_strong_coupling
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:28:26.81354+00:00
-- url     : https://prove2.me/theorems/0447e33c-5bf2-4ac2-b45b-15ca2ac8fbc6
-- title:
--   {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO g corr : ℝ} (hform : thetaO - thetaE = g ^ 2 / 2 + corr) (hEven : sectorGround T P 1 ≤ thetaE + deltaE) (hOdd : thetaO - deltaO ≤ sectorGround T P...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.certified_parity_gap_strong_coupling` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certified_parity_gap_strong_coupling
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.certified_parity_gap_strong_coupling {T P : E →ₗ[ℂ] E}
    {thetaE thetaO deltaE deltaO g corr : ℝ}
    (hform : thetaO - thetaE = g ^ 2 / 2 + corr)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) :
    g ^ 2 / 2 + corr - (deltaO + deltaE)
      ≤ sectorGround T P (-1) - sectorGround T P 1 := by sorry
