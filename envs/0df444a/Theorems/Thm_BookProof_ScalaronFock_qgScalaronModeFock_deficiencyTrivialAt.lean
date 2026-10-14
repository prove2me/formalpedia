-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgScalaronModeFock_deficiencyTrivialAt
-- name    : BookProof.ScalaronFock.qgScalaronModeFock_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:08:31.74552+00:00
-- url     : https://prove2.me/theorems/e682fc27-ed35-4d61-b380-08d29dd0d95d
-- title:
--   `BookProof.ScalaronFock.qgScalaronModeFock_deficiencyTrivialAt` {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (modeFockCore a b M alpha Rc phi) (qgScalaronModeFockHamiltonian a b M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgScalaronModeFock_deficiencyTrivialAt` {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (modeFockCore a b M alpha Rc phi) (qgScalaronModeFockHamiltonian a b M alpha Rc phi) z
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgScalaronModeFock_deficiencyTrivialAt`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgScalaronModeFock_deficiencyTrivialAt
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

theorem BookProof.ScalaronFock.qgScalaronModeFock_deficiencyTrivialAt {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (modeFockCore a b M alpha Rc phi)
      (qgScalaronModeFockHamiltonian a b M alpha Rc phi) z := by sorry
