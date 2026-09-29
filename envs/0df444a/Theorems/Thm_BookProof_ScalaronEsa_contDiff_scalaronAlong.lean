-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_contDiff_scalaronAlong
-- name    : BookProof.ScalaronEsa.contDiff_scalaronAlong
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:42:13.10251+00:00
-- url     : https://prove2.me/theorems/9caf50ec-6a63-47e7-95b6-49ece7c5aee3
-- title:
--   The Lean 4 theorem `contDiff_scalaronAlong` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `contDiff_scalaronAlong` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.contDiff_scalaronAlong
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

theorem BookProof.ScalaronEsa.contDiff_scalaronAlong (M alpha : ℝ) (e : E) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : E => starobinskyV M alpha (inner ℝ x e)) := by sorry
