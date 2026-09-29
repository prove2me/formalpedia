-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_ccEquiv_coe
-- name    : BookProof.ScalaronEsa.ccEquiv_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:41:34.066282+00:00
-- url     : https://prove2.me/theorems/b1cd9f77-77ae-4c45-886c-c0805e3c4b00
-- title:
--   The Lean 4 theorem `ccEquiv_coe` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ccEquiv_coe` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.ccEquiv_coe
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

theorem BookProof.ScalaronEsa.ccEquiv_coe (f : ccSchwartz E) :
    ((ccEquiv E f : ccDomain E) : Lp ℂ 2 (volume : Measure E))
      = (f : 𝓢(E, ℂ)).toLp 2 (volume : Measure E) := by sorry
