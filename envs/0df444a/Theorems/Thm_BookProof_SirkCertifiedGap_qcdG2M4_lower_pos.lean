-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_qcdG2M4_lower_pos
-- name    : BookProof.SirkCertifiedGap.qcdG2M4_lower_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:55:10.191984+00:00
-- url     : https://prove2.me/theorems/e2f97f6d-261c-4a16-9b6c-6029087ab4d7
-- title:
--   : 0 < qcdG2M4.lower
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.qcdG2M4_lower_pos` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.qcdG2M4_lower_pos
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.qcdG2M4_lower_pos : 0 < qcdG2M4.lower := by sorry
