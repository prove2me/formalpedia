-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_ccInclLM_apply
-- name    : BookProof.ScalaronEsa.ccInclLM_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:41:44.685309+00:00
-- url     : https://prove2.me/theorems/4f8749ad-6070-4018-b2ef-8ab5fd7e04ef
-- title:
--   The Lean 4 theorem `ccInclLM_apply` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ccInclLM_apply` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.ccInclLM_apply
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

theorem BookProof.ScalaronEsa.ccInclLM_apply (f : ccSchwartz E) :
    ccInclLM E f = ((f : 𝓢(E, ℂ)).toLp 2 (volume : Measure E)) := by sorry
