-- Prove2me | Theorems.Thm_BookProof_QgTruncationResolvent_momWindow_exhausts
-- name    : BookProof.QgTruncationResolvent.momWindow_exhausts
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T22:56:25.609757+00:00
-- url     : https://prove2.me/theorems/a7e52e91-05f1-44eb-9181-08926745fb61
-- title:
--   `BookProof.QgTruncationResolvent.momWindow_exhausts` (F : Finset CMode) : ∀ᶠ n : ℕ in atTop, ∀ a ∈ F, a ∈ momWindow n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTruncationResolvent`.
--
--   `BookProof.QgTruncationResolvent.momWindow_exhausts` (F : Finset CMode) : ∀ᶠ n : ℕ in atTop, ∀ a ∈ F, a ∈ momWindow n
--
--   Formalization note: Lean 4 identifier `BookProof.QgTruncationResolvent.momWindow_exhausts`.

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.momWindow_exhausts
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
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterQgContinuumModeInstance
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa
open BookProof.QgContinuumModeInstance

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {ι : Type*}
variable (W : WallPot) (Q : QgModeData ι)

theorem BookProof.QgTruncationResolvent.momWindow_exhausts (F : Finset CMode) :
    ∀ᶠ n : ℕ in atTop, ∀ a ∈ F, a ∈ momWindow n := by sorry
