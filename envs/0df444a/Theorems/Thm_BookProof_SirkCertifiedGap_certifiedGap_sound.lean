-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_certifiedGap_sound
-- name    : BookProof.SirkCertifiedGap.certifiedGap_sound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:34:52.542793+00:00
-- url     : https://prove2.me/theorems/a5f13455-6533-44a6-a825-ee3fd4dc1a8c
-- title:
--   {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℕ → ℝ} {m : ℕ} (hEven : sectorGround T P 1 ≤ thetaE m + deltaE m) (hOdd : thetaO m - deltaO m ≤ sectorGround T P (-1)) (hpos : 0 < certifiedGap...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.certifiedGap_sound` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certifiedGap_sound
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.certifiedGap_sound {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℕ → ℝ} {m : ℕ}
    (hEven : sectorGround T P 1 ≤ thetaE m + deltaE m)
    (hOdd : thetaO m - deltaO m ≤ sectorGround T P (-1))
    (hpos : 0 < certifiedGap thetaE thetaO deltaE deltaO m) :
    certifiedGap thetaE thetaO deltaE deltaO m
        ≤ sectorGround T P (-1) - sectorGround T P 1
      ∧ sectorGround T P 1 < sectorGround T P (-1) := by sorry
