-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_le_sectorGround
-- name    : BookProof.SirkCertifiedGap.le_sectorGround
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:36:31.949648+00:00
-- url     : https://prove2.me/theorems/f0767ecd-258f-4244-bb2f-e04ee0723289
-- title:
--   {T P : E →ₗ[ℂ] E} {s c : ℝ} (hne : (sectorRayleighSet T P s).Nonempty) (hlb : ∀ x : E, ‖x‖ = 1 → x ∈ paritySector P s → c ≤ rayleigh T x) : c ≤ sectorGround T P s
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.le_sectorGround` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.le_sectorGround
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.le_sectorGround {T P : E →ₗ[ℂ] E} {s c : ℝ}
    (hne : (sectorRayleighSet T P s).Nonempty)
    (hlb : ∀ x : E, ‖x‖ = 1 → x ∈ paritySector P s → c ≤ rayleigh T x) :
    c ≤ sectorGround T P s := by sorry
