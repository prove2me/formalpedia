-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgScalaronFock_symmetric
-- name    : BookProof.ScalaronFock.qgScalaronFock_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:24:39.021754+00:00
-- url     : https://prove2.me/theorems/05b0ac59-dd0b-400a-b380-9b20068bb34d
-- title:
--   `BookProof.ScalaronFock.qgScalaronFock_symmetric` (M alpha : ℝ) : SymmetricOn qgFockCore (qgScalaronFockHamiltonian M alpha)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgScalaronFock_symmetric` (M alpha : ℝ) : SymmetricOn qgFockCore (qgScalaronFockHamiltonian M alpha)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgScalaronFock_symmetric`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgScalaronFock_symmetric
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

theorem BookProof.ScalaronFock.qgScalaronFock_symmetric (M alpha : ℝ) :
    SymmetricOn qgFockCore (qgScalaronFockHamiltonian M alpha) := by sorry
