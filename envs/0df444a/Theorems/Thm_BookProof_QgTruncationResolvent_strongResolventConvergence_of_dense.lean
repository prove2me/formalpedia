-- Prove2me | Theorems.Thm_BookProof_QgTruncationResolvent_strongResolventConvergence_of_dense
-- name    : BookProof.QgTruncationResolvent.strongResolventConvergence_of_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:37:27.200599+00:00
-- url     : https://prove2.me/theorems/8f7273d7-b780-4e06-80e0-666e13d25161
-- title:
--   `BookProof.QgTruncationResolvent.strongResolventConvergence_of_dense` {T : UnboundedSelfAdjoint F} {S : ℕ → UnboundedSelfAdjoint F} {G : Set F} (hG : Dense G) (h : ∀ y ∈ G, Tendsto
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTruncationResolvent`.
--
--   `BookProof.QgTruncationResolvent.strongResolventConvergence_of_dense` {T : UnboundedSelfAdjoint F} {S : ℕ → UnboundedSelfAdjoint F} {G : Set F} (hG : Dense G) (h : ∀ y ∈ G, Tendsto (fun n => (S n).resCLM 1 y) atTop (𝓝 (T.resCLM 1 y))) : StrongResolventConvergence T S
--
--   Formalization note: Lean 4 identifier `BookProof.QgTruncationResolvent.strongResolventConvergence_of_dense`.

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.strongResolventConvergence_of_dense
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.QgTruncationResolvent.strongResolventConvergence_of_dense {T : UnboundedSelfAdjoint F}
    {S : ℕ → UnboundedSelfAdjoint F} {G : Set F} (hG : Dense G)
    (h : ∀ y ∈ G, Tendsto (fun n => (S n).resCLM 1 y) atTop (𝓝 (T.resCLM 1 y))) :
    StrongResolventConvergence T S := by sorry
