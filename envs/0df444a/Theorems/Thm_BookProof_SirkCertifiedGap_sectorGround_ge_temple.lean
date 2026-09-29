-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_sectorGround_ge_temple
-- name    : BookProof.SirkCertifiedGap.sectorGround_ge_temple
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T10:03:09.773802+00:00
-- url     : https://prove2.me/theorems/b8481ab3-7f65-4712-9fc2-1e5d64074167
-- title:
--   The Lean 4 theorem `sectorGround_ge_temple` in the `ChapterSirkCertifiedGap` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sectorGround_ge_temple` in the `ChapterSirkCertifiedGap` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.sectorGround_ge_temple
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
import Theorems.Thm_BookProof_SirkCertifiedGap_sectorRestrict_isSymmetric
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.sectorGround_ge_temple {T P : E →ₗ[ℂ] E} {s : ℝ}
    (hcomm : ∀ x, T (P x) = P (T x)) (hT : T.IsSymmetric)
    {y : paritySector P s} (hy : ‖y‖ = 1)
    (hne : (univ : Finset (Fin (Module.finrank ℂ (paritySector P s)))).Nonempty)
    {β : ℝ}
    (hsep : ∀ i, (sectorRestrict_isSymmetric (s := s) hcomm hT).eigenvalues (rfl) i
        = sectorGround T P s
      ∨ β ≤ (sectorRestrict_isSymmetric (s := s) hcomm hT).eigenvalues (rfl) i)
    (hβ : rayleigh T (y : E) < β) :
    rayleigh T (y : E)
        - (‖T (y : E)‖ ^ 2 - rayleigh T (y : E) ^ 2) / (β - rayleigh T (y : E))
      ≤ sectorGround T P s := by sorry
