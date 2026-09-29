-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_sectorGround_eq_inf_eigenvalues
-- name    : BookProof.SirkCertifiedGap.sectorGround_eq_inf_eigenvalues
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T10:02:47.635097+00:00
-- url     : https://prove2.me/theorems/860afa50-b28b-4104-a4e6-f12c3d14f07e
-- title:
--   The Lean 4 theorem `sectorGround_eq_inf_eigenvalues` in the `ChapterSirkCertifiedGap` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sectorGround_eq_inf_eigenvalues` in the `ChapterSirkCertifiedGap` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.sectorGround_eq_inf_eigenvalues
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
import Theorems.Thm_BookProof_SirkCertifiedGap_sectorRestrict_isSymmetric
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.sectorGround_eq_inf_eigenvalues {T P : E →ₗ[ℂ] E} {s : ℝ}
    (hcomm : ∀ x, T (P x) = P (T x)) (hT : T.IsSymmetric)
    (hne : (univ : Finset (Fin (Module.finrank ℂ (paritySector P s)))).Nonempty) :
    sectorGround T P s
      = univ.inf' hne fun i =>
          (sectorRestrict_isSymmetric (s := s) hcomm hT).eigenvalues (rfl) i := by sorry
