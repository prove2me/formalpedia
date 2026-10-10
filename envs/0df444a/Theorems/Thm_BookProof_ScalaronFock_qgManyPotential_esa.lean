-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgManyPotential_esa
-- name    : BookProof.ScalaronFock.qgManyPotential_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:24:35.040075+00:00
-- url     : https://prove2.me/theorems/243096ab-8ffc-4d3f-bba5-9d9f17ce5a54
-- title:
--   `BookProof.ScalaronFock.qgManyPotential_esa` (M alpha : ℝ) (n : ℕ) : EssentiallySelfAdjointOn (ccDomain (qgSector n)) (opCc (qgManyPotential M alpha n) (contDiff_qgManyPotential M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgManyPotential_esa` (M alpha : ℝ) (n : ℕ) : EssentiallySelfAdjointOn (ccDomain (qgSector n)) (opCc (qgManyPotential M alpha n) (contDiff_qgManyPotential M alpha n))
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgManyPotential_esa`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgManyPotential_esa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.ScalaronFock.qgManyPotential_esa (M alpha : ℝ) (n : ℕ) :
    EssentiallySelfAdjointOn (ccDomain (qgSector n))
      (opCc (qgManyPotential M alpha n) (contDiff_qgManyPotential M alpha n)) := by sorry
