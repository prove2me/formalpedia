-- Prove2me | Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_truncHam_tendsto
-- name    : BookProof.SqSumOuterFamily.SqFamily.truncHam_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:09:28.959104+00:00
-- url     : https://prove2.me/theorems/fe889ee3-345c-441a-886d-ca5ad0059efa
-- title:
--   `BookProof.SqSumOuterFamily.SqFamily.truncHam_tendsto` (F : SqFamily) (x : outerCore F.dim) : Tendsto (fun N : ℕ => (truncHam F N x : outerFock F.dim)) atTop (𝓝 (F.outerHam x))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqSumOuterSingleTime`.
--
--   `BookProof.SqSumOuterFamily.SqFamily.truncHam_tendsto` (F : SqFamily) (x : outerCore F.dim) : Tendsto (fun N : ℕ => (truncHam F N x : outerFock F.dim)) atTop (𝓝 (F.outerHam x))
--
--   Formalization note: Lean 4 identifier `BookProof.SqSumOuterFamily.SqFamily.truncHam_tendsto`.

-- Generated from ChapterSqSumOuterSingleTime.lean — theorem BookProof.SqSumOuterFamily.SqFamily.truncHam_tendsto
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

theorem BookProof.SqSumOuterFamily.SqFamily.truncHam_tendsto (F : SqFamily) (x : outerCore F.dim) :
    Tendsto (fun N : ℕ => (truncHam F N x : outerFock F.dim)) atTop (𝓝 (F.outerHam x)) := by sorry
