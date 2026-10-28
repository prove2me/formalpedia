-- Prove2me | Theorems.Thm_BookProof_QgTimeStepping_tendsto_iterate_cnStep
-- name    : BookProof.QgTimeStepping.tendsto_iterate_cnStep
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:34:46.124778+00:00
-- url     : https://prove2.me/theorems/5969c3a2-6de0-49c3-8c35-868194b97229
-- title:
--   `BookProof.QgTimeStepping.tendsto_iterate_cnStep` {t : ℝ} (ht : 0 < t) (v : H) : Tendsto (fun k : ℕ => (cnStep T (t / (k + 1)))^[k + 1] v) atTop (𝓝 (T.stoneU t v))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTimeStepping`.
--
--   `BookProof.QgTimeStepping.tendsto_iterate_cnStep` {t : ℝ} (ht : 0 < t) (v : H) : Tendsto (fun k : ℕ => (cnStep T (t / (k + 1)))^[k + 1] v) atTop (𝓝 (T.stoneU t v))
--
--   Formalization note: Lean 4 identifier `BookProof.QgTimeStepping.tendsto_iterate_cnStep`.

-- Generated from ChapterQgTimeStepping.lean — theorem BookProof.QgTimeStepping.tendsto_iterate_cnStep
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgTruncationResolvent
import Mathlib
import Definitions.Def_ChapterQgTimeStepping
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlow
open BookProof.QgTimeStepping



open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgOuterFockCoreFL BookProof.QgTruncationResolvent

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)

theorem BookProof.QgTimeStepping.tendsto_iterate_cnStep {t : ℝ} (ht : 0 < t) (v : H) :
    Tendsto (fun k : ℕ => (cnStep T (t / (k + 1)))^[k + 1] v) atTop
      (𝓝 (T.stoneU t v)) := by sorry
