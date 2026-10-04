-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_wave_add_scalaron_symmetric
-- name    : BookProof.ScalaronEsa.wave_add_scalaron_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T11:33:28.022409+00:00
-- url     : https://prove2.me/theorems/59c758ef-d6ad-414f-b9c6-c37c0176004d
-- title:
--   The Lean 4 theorem `wave_add_scalaron_symmetric` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wave_add_scalaron_symmetric` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.wave_add_scalaron_symmetric
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

theorem BookProof.ScalaronEsa.wave_add_scalaron_symmetric (n : ℕ) (M alpha : ℝ) (e : SpaceTime n) :
    SymmetricOn (ccDomain (SpaceTime n))
      (waveAddSmoothPotential n (fun x => starobinskyV M alpha (inner ℝ x e))
        (contDiff_scalaronAlong M alpha e)) := by sorry
