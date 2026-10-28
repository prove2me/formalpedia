-- Prove2me | Theorems.Thm_BookProof_QgTruncationResolvent_tendsto_resCLM_shift
-- name    : BookProof.QgTruncationResolvent.tendsto_resCLM_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:36:49.141094+00:00
-- url     : https://prove2.me/theorems/79edc5cb-3943-4b10-af1f-d873551b34ba
-- title:
--   `BookProof.QgTruncationResolvent.tendsto_resCLM_shift` (T : UnboundedSelfAdjoint F) (S : ℕ → UnboundedSelfAdjoint F) {x : F} (hT : x ∈ T.domain) (hS : ∀ n, x ∈ (S n).domain) (hconv
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTruncationResolvent`.
--
--   `BookProof.QgTruncationResolvent.tendsto_resCLM_shift` (T : UnboundedSelfAdjoint F) (S : ℕ → UnboundedSelfAdjoint F) {x : F} (hT : x ∈ T.domain) (hS : ∀ n, x ∈ (S n).domain) (hconv : Tendsto (fun n => (S n).op ⟨x, hS n⟩) atTop (𝓝 (T.op ⟨x, hT⟩))) : Tendsto (fun n => (S n).resCLM 1 (T.shift 1 ⟨x, hT⟩)) atTop (𝓝 (T.resCLM 1 (T.shift 1 ⟨x, hT⟩)))
--
--   Formalization note: Lean 4 identifier `BookProof.QgTruncationResolvent.tendsto_resCLM_shift`.

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.tendsto_resCLM_shift
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
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterQgTimeIndependentFlow
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.QgTruncationResolvent.tendsto_resCLM_shift (T : UnboundedSelfAdjoint F) (S : ℕ → UnboundedSelfAdjoint F)
    {x : F} (hT : x ∈ T.domain) (hS : ∀ n, x ∈ (S n).domain)
    (hconv : Tendsto (fun n => (S n).op ⟨x, hS n⟩) atTop (𝓝 (T.op ⟨x, hT⟩))) :
    Tendsto (fun n => (S n).resCLM 1 (T.shift 1 ⟨x, hT⟩)) atTop
      (𝓝 (T.resCLM 1 (T.shift 1 ⟨x, hT⟩))) := by sorry
