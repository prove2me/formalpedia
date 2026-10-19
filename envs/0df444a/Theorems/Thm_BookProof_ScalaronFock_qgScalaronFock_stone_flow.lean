-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgScalaronFock_stone_flow
-- name    : BookProof.ScalaronFock.qgScalaronFock_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:47:57.336982+00:00
-- url     : https://prove2.me/theorems/6d3a8551-2362-4a43-84aa-b2436005257c
-- title:
--   `BookProof.ScalaronFock.qgScalaronFock_stone_flow` (M alpha : ℝ) : ∃ (T : UnboundedSelfAdjoint qgFock) (U : ℝ → (qgFock →L[ℂ] qgFock)), IsSelfAdjointExtension (qgScalaronFockHamilt
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgScalaronFock_stone_flow` (M alpha : ℝ) : ∃ (T : UnboundedSelfAdjoint qgFock) (U : ℝ → (qgFock →L[ℂ] qgFock)), IsSelfAdjointExtension (qgScalaronFockHamiltonian M alpha) T.op ∧ IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgScalaronFock_stone_flow`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgScalaronFock_stone_flow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.StoneBridge
open BookProof.ScalaronFock


open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]

theorem BookProof.ScalaronFock.qgScalaronFock_stone_flow (M alpha : ℝ) :
    ∃ (T : UnboundedSelfAdjoint qgFock) (U : ℝ → (qgFock →L[ℂ] qgFock)),
      IsSelfAdjointExtension (qgScalaronFockHamiltonian M alpha) T.op ∧ IsStoneFlow T U := by sorry
