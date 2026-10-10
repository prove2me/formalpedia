-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_nestedCore_dense
-- name    : BookProof.ScalaronFock.nestedCore_dense
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:22:42.575829+00:00
-- url     : https://prove2.me/theorems/a07b9794-16f8-46c1-9d79-933244069bdd
-- title:
--   `BookProof.ScalaronFock.nestedCore_dense` : Dense ((nestedCore E : Submodule ℂ (nestedFock E)) : Set (nestedFock E))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.nestedCore_dense` : Dense ((nestedCore E : Submodule ℂ (nestedFock E)) : Set (nestedFock E))
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.nestedCore_dense`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.nestedCore_dense
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

theorem BookProof.ScalaronFock.nestedCore_dense :
    Dense ((nestedCore E : Submodule ℂ (nestedFock E)) : Set (nestedFock E)) := by sorry
