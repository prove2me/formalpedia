-- Prove2me | Theorems.Thm_BookProof_VielbeinFock_vielbeinFock_stone_flow
-- name    : BookProof.VielbeinFock.vielbeinFock_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:39:24.887925+00:00
-- url     : https://prove2.me/theorems/18c8f09b-7a7f-47c5-a29c-e652f65037a7
-- title:
--   `BookProof.VielbeinFock.vielbeinFock_stone_flow` (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) : ∃ (T : UnboundedSelfAdjoint (vielbeinFock d)) (U : ℝ → (vielbeinFock d →L[ℂ] vielbeinFock
-- statement:
--   Prove the following Lean 4 theorem from `ChapterVielbeinFiberFock`.
--
--   `BookProof.VielbeinFock.vielbeinFock_stone_flow` (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) : ∃ (T : UnboundedSelfAdjoint (vielbeinFock d)) (U : ℝ → (vielbeinFock d →L[ℂ] vielbeinFock d)), IsSelfAdjointExtension (vielbeinFockHamiltonian M alpha d om) T.op ∧ IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.VielbeinFock.vielbeinFock_stone_flow`.

-- Generated from ChapterVielbeinFiberFock.lean — theorem BookProof.VielbeinFock.vielbeinFock_stone_flow
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.StoneBridge
open BookProof.VielbeinFock


open Filter Topology MeasureTheory


open BookProof.Starobinsky BookProof.ScalaronEsa BookProof.ScalaronFock
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.FarisLavine BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.VielbeinFock.vielbeinFock_stone_flow (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (vielbeinFock d))
      (U : ℝ → (vielbeinFock d →L[ℂ] vielbeinFock d)),
      IsSelfAdjointExtension (vielbeinFockHamiltonian M alpha d om) T.op ∧ IsStoneFlow T U := by sorry
