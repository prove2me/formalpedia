-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_sectorRayleighSet_bddBelow
-- name    : BookProof.SirkCertifiedGap.sectorRayleighSet_bddBelow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:39:26.990622+00:00
-- url     : https://prove2.me/theorems/38b7ab69-2141-4309-8ce8-9f43d90fcdff
-- title:
--   {T : E →ₗ[ℂ] E} (P : E →ₗ[ℂ] E) (s : ℝ) (hT : T.IsSymmetric) : BddBelow (sectorRayleighSet T P s)
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.sectorRayleighSet_bddBelow` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.sectorRayleighSet_bddBelow
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.sectorRayleighSet_bddBelow {T : E →ₗ[ℂ] E} (P : E →ₗ[ℂ] E) (s : ℝ)
    (hT : T.IsSymmetric) : BddBelow (sectorRayleighSet T P s) := by sorry
