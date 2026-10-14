-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_halfDensityUnitary_intertwines
-- name    : BookProof.ScalaronDensitized.halfDensityUnitary_intertwines
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:47:54.377365+00:00
-- url     : https://prove2.me/theorems/f172051d-967f-452c-8478-81f45ee3e0f7
-- title:
--   `BookProof.ScalaronDensitized.halfDensityUnitary_intertwines` (x : physConfCore M alpha) : ((densConfOp M alpha ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure), halfDensityUnitary_mem
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.halfDensityUnitary_intertwines` (x : physConfCore M alpha) : ((densConfOp M alpha ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure), halfDensityUnitary_mem_densConfCore M alpha x⟩ : densConfCore M alpha) : Lp ℂ 2 qgSrcMeasure) = halfDensityUnitary ((physConfOp M alpha x : physConfCore M alpha) : Lp ℂ 2 physMeasure)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.halfDensityUnitary_intertwines`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.halfDensityUnitary_intertwines
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterStarobinskyPotential
import Theorems.Thm_BookProof_ScalaronDensitized_halfDensityUnitary_mem_densConfCore
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity
open BookProof.Starobinsky
open BookProof.ScalaronDensitized



open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)

theorem BookProof.ScalaronDensitized.halfDensityUnitary_intertwines (x : physConfCore M alpha) :
    ((densConfOp M alpha ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure),
        halfDensityUnitary_mem_densConfCore M alpha x⟩ : densConfCore M alpha) :
          Lp ℂ 2 qgSrcMeasure)
      = halfDensityUnitary ((physConfOp M alpha x : physConfCore M alpha) :
          Lp ℂ 2 physMeasure) := by sorry
