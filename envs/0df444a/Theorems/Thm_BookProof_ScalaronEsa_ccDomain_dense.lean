-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_ccDomain_dense
-- name    : BookProof.ScalaronEsa.ccDomain_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:45:45.359988+00:00
-- url     : https://prove2.me/theorems/c6082e26-b904-4fcf-8bd6-5ef2ad58d618
-- title:
--   The Lean 4 theorem `ccDomain_dense` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ccDomain_dense` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.ccDomain_dense
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

theorem BookProof.ScalaronEsa.ccDomain_dense : Dense ((ccDomain E : Submodule ℂ (Lp ℂ 2 (volume : Measure E))) :
    Set (Lp ℂ 2 (volume : Measure E))) := by sorry
