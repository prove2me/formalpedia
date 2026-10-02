-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_quadForm_congr
-- name    : BookProof.QgOuterFockCoreFL.quadForm_congr
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T10:16:41.524121+00:00
-- url     : https://prove2.me/theorems/87983392-4e99-4ea8-ab21-fe4d341c1331
-- title:
--   The Lean 4 theorem `quadForm_congr` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadForm_congr` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockCoreFL.lean

-- Generated from ChapterQgOuterFockCoreFL.lean — theorem BookProof.QgOuterFockCoreFL.quadForm_congr
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterFarisLavineCore
open BookProof.QgOuterFockCoreFL

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.QgOuterFockFL
open BookProof.YangMillsFriedrichs
open BookProof.EsaClosure
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore
open Filter Topology

noncomputable section

theorem BookProof.QgOuterFockCoreFL.quadForm_congr {D D' : Submodule ℂ F} (N : D →ₗ[ℂ] F) (N' : D' →ₗ[ℂ] F)
    (x : D) (x' : D') (hx : (x : F) = (x' : F)) (hN : N x = N' x') :
    quadForm N x = quadForm N' x' := by sorry
