-- Prove2me | Theorems.Thm_BookProof_SmComparisonFull_sm_N_full_stone_flow
-- name    : BookProof.SmComparisonFull.sm_N_full_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T17:55:36.949741+00:00
-- url     : https://prove2.me/theorems/61293715-c550-4f86-906a-82f06564edf2
-- title:
--   `BookProof.SmComparisonFull.sm_N_full_stone_flow` : ∃ (G : UnboundedSelfAdjoint smFullChain.space.carrier) (U : ℝ → (smFullChain.space.carrier →L[ℂ] smFullChain.space.carrier)), Is
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmComparisonFull`.
--
--   `BookProof.SmComparisonFull.sm_N_full_stone_flow` : ∃ (G : UnboundedSelfAdjoint smFullChain.space.carrier) (U : ℝ → (smFullChain.space.carrier →L[ℂ] smFullChain.space.carrier)), IsSelfAdjointExtension smFullChain.op G.op ∧ IsStoneFlow G U
--
--   Formalization note: Lean 4 identifier `BookProof.SmComparisonFull.sm_N_full_stone_flow`.

-- Generated from ChapterSmComparisonFull.lean — theorem BookProof.SmComparisonFull.sm_N_full_stone_flow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterSmComparison
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterSmComparisonFull
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.EsaClosure
open BookProof.StoneBridge



open BookProof.FarisLavine
open BookProof.ScalaronEsa
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open MeasureTheory

noncomputable section

theorem BookProof.SmComparisonFull.sm_N_full_stone_flow :
    ∃ (G : UnboundedSelfAdjoint smFullChain.space.carrier)
      (U : ℝ → (smFullChain.space.carrier →L[ℂ] smFullChain.space.carrier)),
      IsSelfAdjointExtension smFullChain.op G.op ∧ IsStoneFlow G U := by sorry
