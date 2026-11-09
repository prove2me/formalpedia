-- Prove2me | Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_truncHam_esa
-- name    : BookProof.SqSumOuterFamily.SqFamily.truncHam_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:08:38.012206+00:00
-- url     : https://prove2.me/theorems/4f29d128-793a-4fda-bf0e-ea97bb70b918
-- title:
--   `BookProof.SqSumOuterFamily.SqFamily.truncHam_esa` (F : SqFamily) (N : ℕ) : EssentiallySelfAdjointOn (outerCore F.dim) (truncHam F N)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqSumOuterSingleTime`.
--
--   `BookProof.SqSumOuterFamily.SqFamily.truncHam_esa` (F : SqFamily) (N : ℕ) : EssentiallySelfAdjointOn (outerCore F.dim) (truncHam F N)
--
--   Formalization note: Lean 4 identifier `BookProof.SqSumOuterFamily.SqFamily.truncHam_esa`.

-- Generated from ChapterSqSumOuterSingleTime.lean — theorem BookProof.SqSumOuterFamily.SqFamily.truncHam_esa
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
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert BookProof.SirkSingleTime
open BookProof.QgTimeIndependent BookProof.QgTruncationResolvent
open BookProof.DirectSumEsa BookProof.HermiteProductCore

noncomputable section

theorem BookProof.SqSumOuterFamily.SqFamily.truncHam_esa (F : SqFamily) (N : ℕ) :
    EssentiallySelfAdjointOn (outerCore F.dim) (truncHam F N) := by sorry
