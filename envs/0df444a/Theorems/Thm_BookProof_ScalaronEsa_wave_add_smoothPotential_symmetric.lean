-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_wave_add_smoothPotential_symmetric
-- name    : BookProof.ScalaronEsa.wave_add_smoothPotential_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:22:29.018202+00:00
-- url     : https://prove2.me/theorems/971a0ef5-392e-43fa-88de-e6754058303b
-- title:
--   The Lean 4 theorem `wave_add_smoothPotential_symmetric` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wave_add_smoothPotential_symmetric` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.wave_add_smoothPotential_symmetric
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

theorem BookProof.ScalaronEsa.wave_add_smoothPotential_symmetric (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    SymmetricOn (ccDomain (SpaceTime n)) (waveAddSmoothPotential n W hW) := by sorry
