-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_modeFockCore_dense
-- name    : BookProof.ScalaronFock.modeFockCore_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:41:01.826821+00:00
-- url     : https://prove2.me/theorems/f87e17a5-dd5f-45c9-85b7-618872659630
-- title:
--   `BookProof.ScalaronFock.modeFockCore_dense` : Dense ((modeFockCore a b M alpha Rc phi : Submodule ℂ modeFock) : Set modeFock)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.modeFockCore_dense` : Dense ((modeFockCore a b M alpha Rc phi : Submodule ℂ modeFock) : Set modeFock)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.modeFockCore_dense`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.modeFockCore_dense
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.FarisLavine
open BookProof.QuantumGravityDensitized
open BookProof.ScalaronEsa
open BookProof.ScalaronFock


open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]
variable (a b : ℕ → ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℕ → ℝ)

theorem BookProof.ScalaronFock.modeFockCore_dense :
    Dense ((modeFockCore a b M alpha Rc phi : Submodule ℂ modeFock) : Set modeFock) := by sorry
