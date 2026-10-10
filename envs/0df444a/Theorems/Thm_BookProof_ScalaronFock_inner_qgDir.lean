-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_inner_qgDir
-- name    : BookProof.ScalaronFock.inner_qgDir
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:23:27.076462+00:00
-- url     : https://prove2.me/theorems/70c2711c-a475-49fa-bbfb-deead2d8f5f4
-- title:
--   `BookProof.ScalaronFock.inner_qgDir` (n : ℕ) (x : qgSector n) (j : Fin n) (i : Fin 2) : (inner ℝ x (qgDir n j i) : ℝ) = x (j, i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.inner_qgDir` (n : ℕ) (x : qgSector n) (j : Fin n) (i : Fin 2) : (inner ℝ x (qgDir n j i) : ℝ) = x (j, i)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.inner_qgDir`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.inner_qgDir
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

theorem BookProof.ScalaronFock.inner_qgDir (n : ℕ) (x : qgSector n) (j : Fin n) (i : Fin 2) :
    (inner ℝ x (qgDir n j i) : ℝ) = x (j, i) := by sorry
