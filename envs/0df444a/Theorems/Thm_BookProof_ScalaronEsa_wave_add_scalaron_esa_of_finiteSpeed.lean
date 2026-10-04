-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_wave_add_scalaron_esa_of_finiteSpeed
-- name    : BookProof.ScalaronEsa.wave_add_scalaron_esa_of_finiteSpeed
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T11:32:24.779989+00:00
-- url     : https://prove2.me/theorems/3fd12997-471c-44a2-a8b6-70f7db7ca7bb
-- title:
--   The Lean 4 theorem `wave_add_scalaron_esa_of_finiteSpeed` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wave_add_scalaron_esa_of_finiteSpeed` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.wave_add_scalaron_esa_of_finiteSpeed
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
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_scalaronAlong
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

theorem BookProof.ScalaronEsa.wave_add_scalaron_esa_of_finiteSpeed (n : ℕ) (M alpha : ℝ) (e : SpaceTime n)
    (finiteSpeed : ∀ z : ℂ, z.im ≠ 0 →
      DeficiencyTrivialAt (ccDomain (SpaceTime n))
        (waveAddSmoothPotential n (fun x => starobinskyV M alpha (inner ℝ x e))
          (contDiff_scalaronAlong M alpha e)) z) :
    EssentiallySelfAdjointOn (ccDomain (SpaceTime n))
      (waveAddSmoothPotential n (fun x => starobinskyV M alpha (inner ℝ x e))
        (contDiff_scalaronAlong M alpha e)) := by sorry
