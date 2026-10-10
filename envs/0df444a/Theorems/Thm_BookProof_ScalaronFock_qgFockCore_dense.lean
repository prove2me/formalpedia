-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgFockCore_dense
-- name    : BookProof.ScalaronFock.qgFockCore_dense
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:24:38.000556+00:00
-- url     : https://prove2.me/theorems/22794e46-8999-470e-9c57-dc864643bbbf
-- title:
--   `BookProof.ScalaronFock.qgFockCore_dense` : Dense ((qgFockCore : Submodule ℂ qgFock) : Set qgFock)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgFockCore_dense` : Dense ((qgFockCore : Submodule ℂ qgFock) : Set qgFock)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgFockCore_dense`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgFockCore_dense
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
open BookProof.ScalaronFock


open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]

theorem BookProof.ScalaronFock.qgFockCore_dense : Dense ((qgFockCore : Submodule ℂ qgFock) : Set qgFock) := by sorry
