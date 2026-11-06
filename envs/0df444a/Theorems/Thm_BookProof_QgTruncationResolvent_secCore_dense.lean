-- Prove2me | Theorems.Thm_BookProof_QgTruncationResolvent_secCore_dense
-- name    : BookProof.QgTruncationResolvent.secCore_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T13:11:23.717196+00:00
-- url     : https://prove2.me/theorems/cbaf2917-366c-493d-a6dd-6d972a9c2cdc
-- title:
--   `BookProof.QgTruncationResolvent.secCore_dense` : Dense ((secCore (ι
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTruncationResolvent`.
--
--   `BookProof.QgTruncationResolvent.secCore_dense` : Dense ((secCore (ι
--
--   Formalization note: Lean 4 identifier `BookProof.QgTruncationResolvent.secCore_dense`.

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.secCore_dense
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronFiberFL
open BookProof.ScalaronEsa
open BookProof.ScalaronFiberFL
open BookProof.ScalaronFiberFL.WallPot
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {ι : Type*}

theorem BookProof.QgTruncationResolvent.secCore_dense :
    Dense ((secCore (ι := ι) : Submodule ℂ (Sec ι)) : Set (Sec ι)) := by sorry
