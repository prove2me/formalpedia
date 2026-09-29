-- Prove2me | Theorems.Thm_BookProof_SirkGapTable_CouplingCertificate_lo_le_hi
-- name    : BookProof.SirkGapTable.CouplingCertificate.lo_le_hi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:41:46.725029+00:00
-- url     : https://prove2.me/theorems/4d99d98e-00d0-4e9f-a1da-90723699afc7
-- title:
--   (c : CouplingCertificate) : c.lo ≤ c.hi
-- statement:
--   Lean 4 theorem `BookProof.SirkGapTable.CouplingCertificate.lo_le_hi` (module `BookProof.SirkGapTable`), source chapter `BookProof/ChapterSirkGapTable.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.CouplingCertificate.lo_le_hi
import Mathlib
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable
open BookProof.SirkGapTable.CouplingCertificate









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.SirkGapTable.CouplingCertificate.lo_le_hi (c : CouplingCertificate) : c.lo ≤ c.hi := by sorry
