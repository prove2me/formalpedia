-- Prove2me | Theorems.Thm_BookProof_QgTruncationResolvent_isShiftInvertC_neg_resCLM
-- name    : BookProof.QgTruncationResolvent.isShiftInvertC_neg_resCLM
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-02T09:33:50.598128+00:00
-- url     : https://prove2.me/theorems/c036d68d-916d-4186-b940-457386a093e2
-- title:
--   `BookProof.QgTruncationResolvent.isShiftInvertC_neg_resCLM` (T : UnboundedSelfAdjoint F) : IsShiftInvertC T.op Complex.I (-(T.resCLM 1))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTruncationResolvent`.
--
--   `BookProof.QgTruncationResolvent.isShiftInvertC_neg_resCLM` (T : UnboundedSelfAdjoint F) : IsShiftInvertC T.op Complex.I (-(T.resCLM 1))
--
--   Formalization note: Lean 4 identifier `BookProof.QgTruncationResolvent.isShiftInvertC_neg_resCLM`.

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.isShiftInvertC_neg_resCLM
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HashimotoShiftInvert
open BookProof.HashimotoShiftInvert
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
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

theorem BookProof.QgTruncationResolvent.isShiftInvertC_neg_resCLM (T : UnboundedSelfAdjoint F) :
    IsShiftInvertC T.op Complex.I (-(T.resCLM 1)) := by sorry
