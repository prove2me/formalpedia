-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_contDiff_scalaronFullPotential
-- name    : BookProof.ScalaronEsa.contDiff_scalaronFullPotential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:21:20.285492+00:00
-- url     : https://prove2.me/theorems/04c0e081-5ab9-4067-b887-62b30f12d2d4
-- title:
--   The Lean 4 theorem `contDiff_scalaronFullPotential` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `contDiff_scalaronFullPotential` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.contDiff_scalaronFullPotential
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

theorem BookProof.ScalaronEsa.contDiff_scalaronFullPotential (M alpha : ℝ) (eRc ephi : E) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scalaronFullPotential M alpha eRc ephi) := by sorry
