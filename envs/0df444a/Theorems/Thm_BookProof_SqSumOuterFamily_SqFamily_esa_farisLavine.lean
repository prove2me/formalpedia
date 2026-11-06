-- Prove2me | Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_esa_farisLavine
-- name    : BookProof.SqSumOuterFamily.SqFamily.esa_farisLavine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:58:12.954878+00:00
-- url     : https://prove2.me/theorems/9838a555-dad3-4516-a503-940648f01fc0
-- title:
--   `BookProof.SqSumOuterFamily.SqFamily.esa_farisLavine` : EssentiallySelfAdjointOn (outerFriedDom F.dim) (dsFibOp (fun n : ℕ => harmFried (F.dim n)) F.secExt F.flK F.secExt_rel) ∧ ∀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqSumOuterFamily`.
--
--   `BookProof.SqSumOuterFamily.SqFamily.esa_farisLavine` : EssentiallySelfAdjointOn (outerFriedDom F.dim) (dsFibOp (fun n : ℕ => harmFried (F.dim n)) F.secExt F.flK F.secExt_rel) ∧ ∀ x : outerCore F.dim, ∃ h : (x : outerFock F.dim) ∈ outerFriedDom F.dim, dsFibOp (fun n : ℕ => harmFried (F.dim n)) F.secExt F.flK F.secExt_rel ⟨(x : outerFock F.dim), h⟩ = F.outerHam x
--
--   Formalization note: Lean 4 identifier `BookProof.SqSumOuterFamily.SqFamily.esa_farisLavine`.

-- Generated from ChapterSqSumOuterFamily.lean — theorem BookProof.SqSumOuterFamily.SqFamily.esa_farisLavine
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
open BookProof.DirectSumEsa
open BookProof.HermiteProductCore
open BookProof.QgOuterFockFL



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open BookProof.SqSumOuterFamily

noncomputable section

variable (dim : ℕ → ℕ)
variable (F : SqFamily)

theorem BookProof.SqSumOuterFamily.SqFamily.esa_farisLavine :
    EssentiallySelfAdjointOn (outerFriedDom F.dim)
        (dsFibOp (fun n : ℕ => harmFried (F.dim n)) F.secExt F.flK F.secExt_rel) ∧
      ∀ x : outerCore F.dim, ∃ h : (x : outerFock F.dim) ∈ outerFriedDom F.dim,
        dsFibOp (fun n : ℕ => harmFried (F.dim n)) F.secExt F.flK F.secExt_rel
            ⟨(x : outerFock F.dim), h⟩ = F.outerHam x := by sorry
