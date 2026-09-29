-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_mem_ccSchwartz
-- name    : BookProof.ScalaronEsa.mem_ccSchwartz
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:42:22.528688+00:00
-- url     : https://prove2.me/theorems/ebde4c74-e336-4921-9836-c4bc161a573f
-- title:
--   The Lean 4 theorem `mem_ccSchwartz` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mem_ccSchwartz` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.mem_ccSchwartz
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

theorem BookProof.ScalaronEsa.mem_ccSchwartz {f : 𝓢(E, ℂ)} :
    f ∈ ccSchwartz E ↔ HasCompactSupport (f : E → ℂ) := by sorry
