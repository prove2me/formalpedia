-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_deficiencyTrivial
-- name    : BookProof.ScalaronEsa.smoothPotential_deficiencyTrivial
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:22:19.418498+00:00
-- url     : https://prove2.me/theorems/e153d722-15c6-4bae-99ad-e069229dbf8d
-- title:
--   The Lean 4 theorem `smoothPotential_deficiencyTrivial` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `smoothPotential_deficiencyTrivial` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.smoothPotential_deficiencyTrivial
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

theorem BookProof.ScalaronEsa.smoothPotential_deficiencyTrivial (W : E → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (ccDomain E) (opCc W hW) z := by sorry
