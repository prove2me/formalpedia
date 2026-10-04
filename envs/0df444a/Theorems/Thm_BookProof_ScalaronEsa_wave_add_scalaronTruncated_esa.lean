-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_wave_add_scalaronTruncated_esa
-- name    : BookProof.ScalaronEsa.wave_add_scalaronTruncated_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T22:42:28.217751+00:00
-- url     : https://prove2.me/theorems/b88d4b09-f361-466f-947b-6cca34e4e539
-- title:
--   The Lean 4 theorem `wave_add_scalaronTruncated_esa` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wave_add_scalaronTruncated_esa` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.wave_add_scalaronTruncated_esa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWaveUnboundedPotential
open BookProof.Starobinsky
open BookProof.StrichartzWave
open BookProof.ScalaronEsa

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.ScalaronEsa.wave_add_scalaronTruncated_esa (n : ℕ) (M alpha : ℝ) (e : SpaceTime n) (R : ℝ) :
    ∃ WR : SpaceTime n → ℝ, Function.HasTemperateGrowth WR ∧
      (∀ x, ‖x‖ ≤ R → WR x = starobinskyV M alpha (inner ℝ x e)) ∧
      (∀ x, R + 1 ≤ ‖x‖ → WR x = 0) ∧
      EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
        (opL2 (waveOp n 0 + potentialOp WR)) := by sorry
