-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_symmetric
-- name    : BookProof.ScalaronEsa.smoothPotential_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:21:21.406535+00:00
-- url     : https://prove2.me/theorems/73ab8807-0d22-4d7e-b203-e4bb7b789a3d
-- title:
--   The Lean 4 theorem `smoothPotential_symmetric` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `smoothPotential_symmetric` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.smoothPotential_symmetric
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

theorem BookProof.ScalaronEsa.smoothPotential_symmetric (W : E → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    SymmetricOn (ccDomain E) (opCc W hW) := by sorry
