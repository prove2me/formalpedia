-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_sectorRestrict_coe
-- name    : BookProof.SirkCertifiedGap.sectorRestrict_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:40:01.374971+00:00
-- url     : https://prove2.me/theorems/a29c137a-23cd-47c8-89e5-196c2aa92e14
-- title:
--   {T P : E →ₗ[ℂ] E} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x)) (y : paritySector P s) : ((sectorRestrict T P s hcomm) y : E) = T (y : E)
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.sectorRestrict_coe` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.sectorRestrict_coe
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.sectorRestrict_coe {T P : E →ₗ[ℂ] E} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x))
    (y : paritySector P s) : ((sectorRestrict T P s hcomm) y : E) = T (y : E) := by sorry
