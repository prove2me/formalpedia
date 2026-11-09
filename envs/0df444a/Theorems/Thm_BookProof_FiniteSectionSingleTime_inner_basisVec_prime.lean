-- Prove2me | Theorems.Thm_BookProof_FiniteSectionSingleTime_inner_basisVec_prime
-- name    : BookProof.FiniteSectionSingleTime.inner_basisVec_prime
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T20:43:00.543334+00:00
-- url     : https://prove2.me/theorems/87855495-cf1f-4663-9c89-5c950e1427ac
-- title:
--   BookProof.FiniteSectionSingleTime.inner_basisVec'
-- statement:
--   BookProof.FiniteSectionSingleTime.inner_basisVec'

-- Generated from ChapterFiniteSectionSingleTime.lean — theorem BookProof.FiniteSectionSingleTime.inner_basisVec'
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFiniteSectionSingleTime
import Definitions.Def_ChapterE4
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterE4
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterQymTimeIndependentFlow
open BookProof.ChapterE4
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.FiniteSectionSingleTime


open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.QgTruncationResolvent BookProof.SirkSingleTime BookProof.QgTimeIndependent
open BookProof.HashimotoShiftInvert
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato

noncomputable section

variable {ι : Type*} [DecidableEq ι]

theorem BookProof.FiniteSectionSingleTime.inner_basisVec_prime (k : ι) (y : L2I ι) :
    (inner ℂ y (basisVec k) : ℂ) = (starRingEnd ℂ) ((y : ι → ℂ) k) := by sorry
