-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_sectorGround_le_rayleigh
-- name    : BookProof.SirkCertifiedGap.sectorGround_le_rayleigh
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:56:20.415626+00:00
-- url     : https://prove2.me/theorems/46ebbd54-1e62-4acf-af43-6792a951d0df
-- title:
--   {T : E →ₗ[ℂ] E} {P : E →ₗ[ℂ] E} {s : ℝ} (hT : T.IsSymmetric) {x : E} (hx : ‖x‖ = 1) (hmem : x ∈ paritySector P s) : sectorGround T P s ≤ rayleigh T x
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.sectorGround_le_rayleigh` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.sectorGround_le_rayleigh
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.sectorGround_le_rayleigh {T : E →ₗ[ℂ] E} {P : E →ₗ[ℂ] E} {s : ℝ}
    (hT : T.IsSymmetric) {x : E} (hx : ‖x‖ = 1) (hmem : x ∈ paritySector P s) :
    sectorGround T P s ≤ rayleigh T x := by sorry
