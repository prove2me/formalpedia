-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgScalaronFock_esa
-- name    : BookProof.ScalaronFock.qgScalaronFock_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:40:34.669005+00:00
-- url     : https://prove2.me/theorems/64225ca5-35db-4cd1-bc3e-7723be2e81c1
-- title:
--   `BookProof.ScalaronFock.qgScalaronFock_esa` (M alpha : ℝ) : EssentiallySelfAdjointOn qgFockCore (qgScalaronFockHamiltonian M alpha)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgScalaronFock_esa` (M alpha : ℝ) : EssentiallySelfAdjointOn qgFockCore (qgScalaronFockHamiltonian M alpha)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgScalaronFock_esa`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgScalaronFock_esa
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
import Definitions.Def_ChapterFarisLavineCore
open BookProof.ScalaronFock


open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]

theorem BookProof.ScalaronFock.qgScalaronFock_esa (M alpha : ℝ) :
    EssentiallySelfAdjointOn qgFockCore (qgScalaronFockHamiltonian M alpha) := by sorry
