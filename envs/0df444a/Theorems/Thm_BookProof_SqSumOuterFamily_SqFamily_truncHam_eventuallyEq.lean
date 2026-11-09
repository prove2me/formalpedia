-- Prove2me | Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_truncHam_eventuallyEq
-- name    : BookProof.SqSumOuterFamily.SqFamily.truncHam_eventuallyEq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:09:13.452981+00:00
-- url     : https://prove2.me/theorems/c6ab2e65-a5ae-40cb-ba60-652300fd8304
-- title:
--   `BookProof.SqSumOuterFamily.SqFamily.truncHam_eventuallyEq` (F : SqFamily) (x : outerCore F.dim) : ∀ᶠ N in atTop, (truncHam F N x : outerFock F.dim) = F.outerHam x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqSumOuterSingleTime`.
--
--   `BookProof.SqSumOuterFamily.SqFamily.truncHam_eventuallyEq` (F : SqFamily) (x : outerCore F.dim) : ∀ᶠ N in atTop, (truncHam F N x : outerFock F.dim) = F.outerHam x
--
--   Formalization note: Lean 4 identifier `BookProof.SqSumOuterFamily.SqFamily.truncHam_eventuallyEq`.

-- Generated from ChapterSqSumOuterSingleTime.lean — theorem BookProof.SqSumOuterFamily.SqFamily.truncHam_eventuallyEq
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

theorem BookProof.SqSumOuterFamily.SqFamily.truncHam_eventuallyEq (F : SqFamily) (x : outerCore F.dim) :
    ∀ᶠ N in atTop, (truncHam F N x : outerFock F.dim) = F.outerHam x := by sorry
