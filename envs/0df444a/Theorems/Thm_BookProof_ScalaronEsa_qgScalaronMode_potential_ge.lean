-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_qgScalaronMode_potential_ge
-- name    : BookProof.ScalaronEsa.qgScalaronMode_potential_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:33:38.153852+00:00
-- url     : https://prove2.me/theorems/58ffec19-d60a-48dd-bc56-4a3045f54769
-- title:
--   The Lean 4 theorem `qgScalaronMode_potential_ge` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgScalaronMode_potential_ge` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.qgScalaronMode_potential_ge
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.ScalaronEsa


open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℝ)

theorem BookProof.ScalaronEsa.qgScalaronMode_potential_ge (halpha : 0 < alpha) (k : ℕ) :
    -(M ^ 4 / (16 * alpha)) ≤ qgScalaronModePotential M alpha Rc phi k := by sorry
