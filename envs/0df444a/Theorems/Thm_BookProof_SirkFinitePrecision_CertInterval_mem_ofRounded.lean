-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_mem_ofRounded
-- name    : BookProof.SirkFinitePrecision.CertInterval.mem_ofRounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:46:54.274981+00:00
-- url     : https://prove2.me/theorems/41055919-8b38-4ad5-9e73-0fd51928fe27
-- title:
--   The outward-rounding model.** A floating-point computation delivers a pair of endpoints; directed (outward) rounding guarantees that the rounded lower endpoint lies below, and the rounded
-- statement:
--   **The outward-rounding model.**  A floating-point computation delivers a pair of
--   endpoints; directed (outward) rounding guarantees that the rounded lower endpoint lies
--   below, and the rounded upper endpoint above, the exact value.  That guarantee — and
--   nothing about the floating-point values themselves — is what the certificate
--   consumes.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.CertInterval.mem_ofRounded` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 434–440.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L434-L440

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.CertInterval.mem_ofRounded
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.CertInterval.mem_ofRounded {x lo hi : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    (CertInterval.mk lo hi).Mem x := by sorry
