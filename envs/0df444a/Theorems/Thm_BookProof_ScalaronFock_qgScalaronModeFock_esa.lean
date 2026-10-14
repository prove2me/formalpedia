-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgScalaronModeFock_esa
-- name    : BookProof.ScalaronFock.qgScalaronModeFock_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:08:55.645131+00:00
-- url     : https://prove2.me/theorems/5ee07e5c-9d86-4b6f-86d5-6e8c3075e9c9
-- title:
--   `BookProof.ScalaronFock.qgScalaronModeFock_esa` : EssentiallySelfAdjointOn (modeFockCore a b M alpha Rc phi) (qgScalaronModeFockHamiltonian a b M alpha Rc phi)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgScalaronModeFock_esa` : EssentiallySelfAdjointOn (modeFockCore a b M alpha Rc phi) (qgScalaronModeFockHamiltonian a b M alpha Rc phi)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgScalaronModeFock_esa`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgScalaronModeFock_esa
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.FarisLavine
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

theorem BookProof.ScalaronFock.qgScalaronModeFock_esa :
    EssentiallySelfAdjointOn (modeFockCore a b M alpha Rc phi)
      (qgScalaronModeFockHamiltonian a b M alpha Rc phi) := by sorry
