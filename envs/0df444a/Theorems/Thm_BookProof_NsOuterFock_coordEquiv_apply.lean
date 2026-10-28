-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_coordEquiv_apply
-- name    : BookProof.NsOuterFock.coordEquiv_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:27:59.722375+00:00
-- url     : https://prove2.me/theorems/44001dcd-d78f-47f5-a98d-5cd9f8876e37
-- title:
--   `BookProof.NsOuterFock.coordEquiv_apply` {n : ℕ} (p : Fin n) (l : NsLoc) : coordEquiv n (p, l) = coordOf p l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.coordEquiv_apply` {n : ℕ} (p : Fin n) (l : NsLoc) : coordEquiv n (p, l) = coordOf p l
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.coordEquiv_apply`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.coordEquiv_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterSqSumOuterFamily
import Mathlib
import Definitions.Def_ChapterNsOuterFockFarisLavine
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterShiftedQuadraticEsa



open Finset MvPolynomial
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL

noncomputable section

theorem BookProof.NsOuterFock.coordEquiv_apply {n : ℕ} (p : Fin n) (l : NsLoc) :
    coordEquiv n (p, l) = coordOf p l := by sorry
