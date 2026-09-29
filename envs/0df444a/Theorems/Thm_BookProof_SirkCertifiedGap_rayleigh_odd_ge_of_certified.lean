-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_rayleigh_odd_ge_of_certified
-- name    : BookProof.SirkCertifiedGap.rayleigh_odd_ge_of_certified
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:35:12.428627+00:00
-- url     : https://prove2.me/theorems/9e9adf86-cb9f-4e35-ae83-847c65812aa3
-- title:
--   {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ} (hT : T.IsSymmetric) (hEven : sectorGround T P 1 ≤ thetaE + deltaE) (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) {x : E} (hx : ‖x‖ = 1)...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.rayleigh_odd_ge_of_certified` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.rayleigh_odd_ge_of_certified
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.rayleigh_odd_ge_of_certified {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ}
    (hT : T.IsSymmetric)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1))
    {x : E} (hx : ‖x‖ = 1) (hmem : x ∈ paritySector P (-1)) :
    sectorGround T P 1 + (thetaO - thetaE - (deltaO + deltaE)) ≤ rayleigh T x := by sorry
