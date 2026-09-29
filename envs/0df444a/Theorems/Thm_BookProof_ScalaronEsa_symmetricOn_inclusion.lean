-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_symmetricOn_inclusion
-- name    : BookProof.ScalaronEsa.symmetricOn_inclusion
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:20:28.710268+00:00
-- url     : https://prove2.me/theorems/b6cfefad-7982-4fcd-b8f7-340d52eea1e8
-- title:
--   The Lean 4 theorem `symmetricOn_inclusion` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `symmetricOn_inclusion` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.symmetricOn_inclusion
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

theorem BookProof.ScalaronEsa.symmetricOn_inclusion {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {D D' : Submodule ℂ F} (h : D ≤ D') (T : D' →ₗ[ℂ] F) (hT : SymmetricOn D' T) :
    SymmetricOn D (T ∘ₗ Submodule.inclusion h) := by sorry
