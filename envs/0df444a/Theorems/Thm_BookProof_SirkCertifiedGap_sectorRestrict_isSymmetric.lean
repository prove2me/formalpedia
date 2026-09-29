-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_sectorRestrict_isSymmetric
-- name    : BookProof.SirkCertifiedGap.sectorRestrict_isSymmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:41:05.867332+00:00
-- url     : https://prove2.me/theorems/63f5c9a3-9c68-440d-ab91-803e4377c478
-- title:
--   {T P : E →ₗ[ℂ] E} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x)) (hT : T.IsSymmetric) : (sectorRestrict T P s hcomm).IsSymmetric
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.sectorRestrict_isSymmetric` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.sectorRestrict_isSymmetric
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.sectorRestrict_isSymmetric {T P : E →ₗ[ℂ] E} {s : ℝ}
    (hcomm : ∀ x, T (P x) = P (T x)) (hT : T.IsSymmetric) :
    (sectorRestrict T P s hcomm).IsSymmetric := by sorry
