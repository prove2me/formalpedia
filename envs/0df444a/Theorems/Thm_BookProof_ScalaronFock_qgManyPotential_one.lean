-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgManyPotential_one
-- name    : BookProof.ScalaronFock.qgManyPotential_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:24:07.201477+00:00
-- url     : https://prove2.me/theorems/8192b8f2-8407-44fd-b2bf-22fe4e844789
-- title:
--   `BookProof.ScalaronFock.qgManyPotential_one` (M alpha : ℝ) (x : qgSector 1) : qgManyPotential M alpha 1 x = scalaronFullPotential M alpha (qgDir 1 0 0) (qgDir 1 0 1) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgManyPotential_one` (M alpha : ℝ) (x : qgSector 1) : qgManyPotential M alpha 1 x = scalaronFullPotential M alpha (qgDir 1 0 0) (qgDir 1 0 1) x
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgManyPotential_one`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgManyPotential_one
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.ScalaronEsa
open BookProof.ScalaronFock


open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]

theorem BookProof.ScalaronFock.qgManyPotential_one (M alpha : ℝ) (x : qgSector 1) :
    qgManyPotential M alpha 1 x
      = scalaronFullPotential M alpha (qgDir 1 0 0) (qgDir 1 0 1) x := by sorry
