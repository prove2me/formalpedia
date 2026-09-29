-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_mem_widen
-- name    : BookProof.SirkFinitePrecision.CertInterval.mem_widen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:48:26.424642+00:00
-- url     : https://prove2.me/theorems/3184be34-be39-430a-977f-5f66eaa068e3
-- title:
--   Widening an interval preserves membership
-- statement:
--   Widening an interval preserves membership.
--
--   If $x$ lies in $I$ then $x$ also lies in every widening of $I$ (an outward expansion used to model directed/outward rounding): $I\ni x \Longrightarrow \text{widen}(I)\ni x$.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.CertInterval.mem_widen` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 430–432.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L430-L432

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.CertInterval.mem_widen
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.CertInterval.mem_widen {I : CertInterval} {x ε : ℝ} (hx : I.Mem x) (hε : 0 ≤ ε) :
    (I.widen ε).Mem x := by sorry
