-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_resolvent_mapsTo_paritySector
-- name    : BookProof.SirkCertifiedGap.resolvent_mapsTo_paritySector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:55:42.862686+00:00
-- url     : https://prove2.me/theorems/ec5d618d-ce36-462b-bca5-fa0d201241d7
-- title:
--   {T P R : E →ₗ[ℂ] E} {z : ℂ} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x)) (hR1 : ∀ x, R (T x - z • x) = x) (hR2 : ∀ x, T (R x) - z • R x = x) {x : E} (hx : x ∈ paritySector P s) : R x ∈ paritySector P s
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.resolvent_mapsTo_paritySector` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.resolvent_mapsTo_paritySector
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.resolvent_mapsTo_paritySector {T P R : E →ₗ[ℂ] E} {z : ℂ} {s : ℝ}
    (hcomm : ∀ x, T (P x) = P (T x))
    (hR1 : ∀ x, R (T x - z • x) = x) (hR2 : ∀ x, T (R x) - z • R x = x)
    {x : E} (hx : x ∈ paritySector P s) : R x ∈ paritySector P s := by sorry
