-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgManyPotential_ge
-- name    : BookProof.ScalaronFock.qgManyPotential_ge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:23:23.75599+00:00
-- url     : https://prove2.me/theorems/1ca306d7-151b-45b4-9377-50ce6bd0caca
-- title:
--   `BookProof.ScalaronFock.qgManyPotential_ge` {M alpha : ℝ} (halpha : 0 < alpha) (n : ℕ) (x : qgSector n) : -(n * (M ^ 4 / (16 * alpha))) ≤ qgManyPotential M alpha n x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgManyPotential_ge` {M alpha : ℝ} (halpha : 0 < alpha) (n : ℕ) (x : qgSector n) : -(n * (M ^ 4 / (16 * alpha))) ≤ qgManyPotential M alpha n x
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgManyPotential_ge`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgManyPotential_ge
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

theorem BookProof.ScalaronFock.qgManyPotential_ge {M alpha : ℝ} (halpha : 0 < alpha) (n : ℕ) (x : qgSector n) :
    -(n * (M ^ 4 / (16 * alpha))) ≤ qgManyPotential M alpha n x := by sorry
