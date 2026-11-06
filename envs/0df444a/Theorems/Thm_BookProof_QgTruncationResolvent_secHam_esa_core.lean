-- Prove2me | Theorems.Thm_BookProof_QgTruncationResolvent_secHam_esa_core
-- name    : BookProof.QgTruncationResolvent.secHam_esa_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T13:11:24.644424+00:00
-- url     : https://prove2.me/theorems/547acf37-8850-4637-bb37-1eaa7ca663ff
-- title:
--   `BookProof.QgTruncationResolvent.secHam_esa_core` : EssentiallySelfAdjointOn (secCore (ι
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTruncationResolvent`.
--
--   `BookProof.QgTruncationResolvent.secHam_esa_core` : EssentiallySelfAdjointOn (secCore (ι
--
--   Formalization note: Lean 4 identifier `BookProof.QgTruncationResolvent.secHam_esa_core`.

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.secHam_esa_core
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronFiberFL
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
variable (W : WallPot) (Q : QgModeData ι)

theorem BookProof.QgTruncationResolvent.secHam_esa_core : EssentiallySelfAdjointOn (secCore (ι := ι)) (secHam W Q) := by sorry
