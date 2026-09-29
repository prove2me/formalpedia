-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_rayleigh_sectorRestrict
-- name    : BookProof.SirkCertifiedGap.rayleigh_sectorRestrict
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:38:16.449437+00:00
-- url     : https://prove2.me/theorems/a79391c2-e295-43e1-928c-242a2af97b53
-- title:
--   {T P : E →ₗ[ℂ] E} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x)) (y : paritySector P s) : rayleigh (sectorRestrict T P s hcomm) y = rayleigh T (y : E)
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.rayleigh_sectorRestrict` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.rayleigh_sectorRestrict
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.rayleigh_sectorRestrict {T P : E →ₗ[ℂ] E} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x))
    (y : paritySector P s) : rayleigh (sectorRestrict T P s hcomm) y = rayleigh T (y : E) := by sorry
