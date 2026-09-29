-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_wave_add_smoothPotential_esa_of_finiteSpeed
-- name    : BookProof.ScalaronEsa.wave_add_smoothPotential_esa_of_finiteSpeed
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:20:28.482562+00:00
-- url     : https://prove2.me/theorems/4a8ae473-c2a0-471b-9816-e5aff42e95c2
-- title:
--   The Lean 4 theorem `wave_add_smoothPotential_esa_of_finiteSpeed` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wave_add_smoothPotential_esa_of_finiteSpeed` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.wave_add_smoothPotential_esa_of_finiteSpeed
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

theorem BookProof.ScalaronEsa.wave_add_smoothPotential_esa_of_finiteSpeed (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (finiteSpeed : ∀ z : ℂ, z.im ≠ 0 →
      DeficiencyTrivialAt (ccDomain (SpaceTime n)) (waveAddSmoothPotential n W hW) z) :
    EssentiallySelfAdjointOn (ccDomain (SpaceTime n)) (waveAddSmoothPotential n W hW) := by sorry
