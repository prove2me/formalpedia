-- Prove2me | Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_trunc_secHam_eq_of_le
-- name    : BookProof.SqSumOuterFamily.SqFamily.trunc_secHam_eq_of_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:08:57.353732+00:00
-- url     : https://prove2.me/theorems/8e026fee-b5ee-4060-9c80-41781fb6fa92
-- title:
--   `BookProof.SqSumOuterFamily.SqFamily.trunc_secHam_eq_of_le` (F : SqFamily) {N n : ℕ} (h : n ≤ N) : (F.trunc N).secHam n = F.secHam n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqSumOuterSingleTime`.
--
--   `BookProof.SqSumOuterFamily.SqFamily.trunc_secHam_eq_of_le` (F : SqFamily) {N n : ℕ} (h : n ≤ N) : (F.trunc N).secHam n = F.secHam n
--
--   Formalization note: Lean 4 identifier `BookProof.SqSumOuterFamily.SqFamily.trunc_secHam_eq_of_le`.

-- Generated from ChapterSqSumOuterSingleTime.lean — theorem BookProof.SqSumOuterFamily.SqFamily.trunc_secHam_eq_of_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterSqSumOuterSingleTime
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore
open BookProof.QgOuterFock



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert BookProof.SirkSingleTime
open BookProof.QgTimeIndependent BookProof.QgTruncationResolvent
open BookProof.DirectSumEsa BookProof.HermiteProductCore

noncomputable section

theorem BookProof.SqSumOuterFamily.SqFamily.trunc_secHam_eq_of_le (F : SqFamily) {N n : ℕ} (h : n ≤ N) :
    (F.trunc N).secHam n = F.secHam n := by sorry
