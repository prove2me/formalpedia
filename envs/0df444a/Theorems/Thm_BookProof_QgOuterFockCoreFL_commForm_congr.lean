-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_commForm_congr
-- name    : BookProof.QgOuterFockCoreFL.commForm_congr
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T10:15:48.457916+00:00
-- url     : https://prove2.me/theorems/dce8ea84-f488-42b5-a4ad-9861fd61b2d9
-- title:
--   The Lean 4 theorem `commForm_congr` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `commForm_congr` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockCoreFL.lean

-- Generated from ChapterQgOuterFockCoreFL.lean — theorem BookProof.QgOuterFockCoreFL.commForm_congr
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

theorem BookProof.QgOuterFockCoreFL.commForm_congr {D D' : Submodule ℂ F} (H N : D →ₗ[ℂ] F) (H' N' : D' →ₗ[ℂ] F)
    (x : D) (x' : D') (hH : H x = H' x') (hN : N x = N' x') :
    commForm H N x = commForm H' N' x' := by sorry
