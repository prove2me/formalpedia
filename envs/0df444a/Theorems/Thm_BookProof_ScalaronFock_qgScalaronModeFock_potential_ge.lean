-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgScalaronModeFock_potential_ge
-- name    : BookProof.ScalaronFock.qgScalaronModeFock_potential_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:41:02.072714+00:00
-- url     : https://prove2.me/theorems/4b152310-ff34-4a16-b4a3-06f3a5e27600
-- title:
--   `BookProof.ScalaronFock.qgScalaronModeFock_potential_ge` (halpha : 0 < alpha) (n k : ℕ) : -(M ^ 4 / (16 * alpha)) ≤ qgScalaronModePotential M alpha (Rc n) (phi n) k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgScalaronModeFock_potential_ge` (halpha : 0 < alpha) (n k : ℕ) : -(M ^ 4 / (16 * alpha)) ≤ qgScalaronModePotential M alpha (Rc n) (phi n) k
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgScalaronModeFock_potential_ge`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgScalaronModeFock_potential_ge
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
variable (a b : ℕ → ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℕ → ℝ)

theorem BookProof.ScalaronFock.qgScalaronModeFock_potential_ge (halpha : 0 < alpha) (n k : ℕ) :
    -(M ^ 4 / (16 * alpha)) ≤ qgScalaronModePotential M alpha (Rc n) (phi n) k := by sorry
