-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgManyPotential_apply
-- name    : BookProof.ScalaronFock.qgManyPotential_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:23:46.30598+00:00
-- url     : https://prove2.me/theorems/a76f0913-4fad-468d-bcb4-6b001a354a0c
-- title:
--   `BookProof.ScalaronFock.qgManyPotential_apply` (M alpha : ℝ) (n : ℕ) (x : qgSector n) : qgManyPotential M alpha n x = ∑ j : Fin n, (confV M alpha (x (j, 0)) + starobinskyV M alpha
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgManyPotential_apply` (M alpha : ℝ) (n : ℕ) (x : qgSector n) : qgManyPotential M alpha n x = ∑ j : Fin n, (confV M alpha (x (j, 0)) + starobinskyV M alpha (x (j, 1)))
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgManyPotential_apply`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgManyPotential_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.ScalaronEsa
open BookProof.Starobinsky
open BookProof.ScalaronFock


open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]

theorem BookProof.ScalaronFock.qgManyPotential_apply (M alpha : ℝ) (n : ℕ) (x : qgSector n) :
    qgManyPotential M alpha n x
      = ∑ j : Fin n, (confV M alpha (x (j, 0)) + starobinskyV M alpha (x (j, 1))) := by sorry
