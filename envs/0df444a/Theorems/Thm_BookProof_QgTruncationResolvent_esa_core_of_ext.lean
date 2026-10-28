-- Prove2me | Theorems.Thm_BookProof_QgTruncationResolvent_esa_core_of_ext
-- name    : BookProof.QgTruncationResolvent.esa_core_of_ext
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:36:30.463849+00:00
-- url     : https://prove2.me/theorems/fdeeb1be-a47e-4a10-8f48-2fc18d3bdbf0
-- title:
--   `BookProof.QgTruncationResolvent.esa_core_of_ext` (d : CoreData F) (hesa : EssentiallySelfAdjointOn d.C.dom d.ext) : EssentiallySelfAdjointOn d.C₀ d.H₀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTruncationResolvent`.
--
--   `BookProof.QgTruncationResolvent.esa_core_of_ext` (d : CoreData F) (hesa : EssentiallySelfAdjointOn d.C.dom d.ext) : EssentiallySelfAdjointOn d.C₀ d.H₀
--
--   Formalization note: Lean 4 identifier `BookProof.QgTruncationResolvent.esa_core_of_ext`.

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.esa_core_of_ext
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgTimeIndependentFlow
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.QgTruncationResolvent.esa_core_of_ext (d : CoreData F) (hesa : EssentiallySelfAdjointOn d.C.dom d.ext) :
    EssentiallySelfAdjointOn d.C₀ d.H₀ := by sorry
