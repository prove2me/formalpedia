-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_scalaronFullPotential_ge
-- name    : BookProof.ScalaronEsa.scalaronFullPotential_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:44:11.286969+00:00
-- url     : https://prove2.me/theorems/94f87fe1-d9e4-434a-acf0-d9444649e136
-- title:
--   The Lean 4 theorem `scalaronFullPotential_ge` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `scalaronFullPotential_ge` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.scalaronFullPotential_ge
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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem BookProof.ScalaronEsa.scalaronFullPotential_ge {M alpha : ℝ} (halpha : 0 < alpha) (eRc ephi : E) (x : E) :
    -(M ^ 4 / (16 * alpha)) ≤ scalaronFullPotential M alpha eRc ephi x := by sorry
