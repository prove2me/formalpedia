-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_starobinskyV_not_hasTemperateGrowth
-- name    : BookProof.ScalaronEsa.starobinskyV_not_hasTemperateGrowth
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:20:27.92447+00:00
-- url     : https://prove2.me/theorems/49b85afa-32f9-4870-9998-eae0b10f79d7
-- title:
--   The Lean 4 theorem `starobinskyV_not_hasTemperateGrowth` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyV_not_hasTemperateGrowth` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.starobinskyV_not_hasTemperateGrowth
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

theorem BookProof.ScalaronEsa.starobinskyV_not_hasTemperateGrowth {M alpha : ℝ} (hM : 0 < M) (halpha : 0 < alpha) :
    ¬ Function.HasTemperateGrowth (fun phi : ℝ => starobinskyV M alpha phi) := by sorry
