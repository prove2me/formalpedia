-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_resolvent_commutes_parity
-- name    : BookProof.SirkCertifiedGap.resolvent_commutes_parity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:38:51.869003+00:00
-- url     : https://prove2.me/theorems/cdd78f3b-7350-4d74-bff2-0bc1897f2910
-- title:
--   {T P R : E →ₗ[ℂ] E} {z : ℂ} (hcomm : ∀ x, T (P x) = P (T x)) (hR1 : ∀ x, R (T x - z • x) = x) (hR2 : ∀ x, T (R x) - z • R x = x) (x : E) : R (P x) = P (R x)
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.resolvent_commutes_parity` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.resolvent_commutes_parity
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.resolvent_commutes_parity {T P R : E →ₗ[ℂ] E} {z : ℂ}
    (hcomm : ∀ x, T (P x) = P (T x))
    (hR1 : ∀ x, R (T x - z • x) = x) (hR2 : ∀ x, T (R x) - z • R x = x) (x : E) :
    R (P x) = P (R x) := by sorry
