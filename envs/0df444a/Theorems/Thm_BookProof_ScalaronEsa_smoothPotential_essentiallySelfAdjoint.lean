-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_essentiallySelfAdjoint
-- name    : BookProof.ScalaronEsa.smoothPotential_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:23:17.301997+00:00
-- url     : https://prove2.me/theorems/c4c609f5-e58c-4a61-9be6-9733838fa2de
-- title:
--   The Lean 4 theorem `smoothPotential_essentiallySelfAdjoint` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `smoothPotential_essentiallySelfAdjoint` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.smoothPotential_essentiallySelfAdjoint
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

theorem BookProof.ScalaronEsa.smoothPotential_essentiallySelfAdjoint (W : E → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    EssentiallySelfAdjointOn (ccDomain E) (opCc W hW) := by sorry
