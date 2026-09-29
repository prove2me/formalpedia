-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_waveCc_symmetric
-- name    : BookProof.ScalaronEsa.waveCc_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:21:45.394985+00:00
-- url     : https://prove2.me/theorems/827b7ebd-36b7-4d2a-ab66-19c172a630e2
-- title:
--   The Lean 4 theorem `waveCc_symmetric` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `waveCc_symmetric` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.waveCc_symmetric
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

theorem BookProof.ScalaronEsa.waveCc_symmetric (n : ℕ) : SymmetricOn (ccDomain (SpaceTime n)) (waveCc n) := by sorry
