-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_qgScalaronMode_symmetric
-- name    : BookProof.ScalaronEsa.qgScalaronMode_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T22:42:02.101268+00:00
-- url     : https://prove2.me/theorems/9aba824c-fa03-4a06-9c4b-11d4ffe6f9f1
-- title:
--   The Lean 4 theorem `qgScalaronMode_symmetric` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgScalaronMode_symmetric` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.qgScalaronMode_symmetric
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQuantumGravityDensitized
open BookProof.FarisLavine
open BookProof.QuantumGravityDensitized
open BookProof.ScalaronEsa

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℝ)


open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.ScalaronEsa.qgScalaronMode_symmetric :
    SymmetricOn (mulSymbolDomain (qgModeSymbol a b (qgScalaronModePotential M alpha Rc phi)))
      (qgScalaronModeHamiltonian a b M alpha Rc phi) := by sorry
