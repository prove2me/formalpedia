-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_scalaronFullPotential_essentiallySelfAdjoint
-- name    : BookProof.ScalaronEsa.scalaronFullPotential_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-03T11:33:32.096983+00:00
-- url     : https://prove2.me/theorems/95147bec-0c03-482d-8a6a-0485ba706c24
-- title:
--   The Lean 4 theorem `scalaronFullPotential_essentiallySelfAdjoint` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `scalaronFullPotential_essentiallySelfAdjoint` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.scalaronFullPotential_essentiallySelfAdjoint
import Definitions.Def_ChapterStrichartzWave
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
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_scalaronFullPotential
open BookProof.ScalaronEsa

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.ScalaronEsa.scalaronFullPotential_essentiallySelfAdjoint (M alpha : ℝ) (eRc ephi : E) :
    EssentiallySelfAdjointOn (ccDomain E)
      (opCc (scalaronFullPotential M alpha eRc ephi)
        (contDiff_scalaronFullPotential M alpha eRc ephi)) := by sorry
