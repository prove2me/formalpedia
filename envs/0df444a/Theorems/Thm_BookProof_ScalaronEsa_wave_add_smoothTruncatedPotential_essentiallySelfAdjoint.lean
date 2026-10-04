-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_wave_add_smoothTruncatedPotential_essentiallySelfAdjoint
-- name    : BookProof.ScalaronEsa.wave_add_smoothTruncatedPotential_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T22:42:00.844106+00:00
-- url     : https://prove2.me/theorems/6611be72-d56f-425e-aa42-94859bfc36e4
-- title:
--   The Lean 4 theorem `wave_add_smoothTruncatedPotential_essentiallySelfAdjoint` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wave_add_smoothTruncatedPotential_essentiallySelfAdjoint` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.wave_add_smoothTruncatedPotential_essentiallySelfAdjoint
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWaveUnboundedPotential
open BookProof.StrichartzWave
open BookProof.ScalaronEsa

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.ScalaronEsa.wave_add_smoothTruncatedPotential_essentiallySelfAdjoint (n : ℕ)
    (W : SpaceTime n → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (R : ℝ) :
    ∃ WR : SpaceTime n → ℝ, Function.HasTemperateGrowth WR ∧
      (∀ x, ‖x‖ ≤ R → WR x = W x) ∧ (∀ x, R + 1 ≤ ‖x‖ → WR x = 0) ∧
      EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
        (opL2 (waveOp n 0 + potentialOp WR)) := by sorry
