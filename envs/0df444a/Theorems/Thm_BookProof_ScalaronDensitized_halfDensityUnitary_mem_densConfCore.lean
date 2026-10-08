-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_halfDensityUnitary_mem_densConfCore
-- name    : BookProof.ScalaronDensitized.halfDensityUnitary_mem_densConfCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:14:58.858628+00:00
-- url     : https://prove2.me/theorems/9abada96-0861-4bf9-8e2e-14efa574f216
-- title:
--   `BookProof.ScalaronDensitized.halfDensityUnitary_mem_densConfCore` (x : physConfCore M alpha) : halfDensityUnitary (x : Lp ℂ 2 physMeasure) ∈ densConfCore M alpha
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.halfDensityUnitary_mem_densConfCore` (x : physConfCore M alpha) : halfDensityUnitary (x : Lp ℂ 2 physMeasure) ∈ densConfCore M alpha
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.halfDensityUnitary_mem_densConfCore`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.halfDensityUnitary_mem_densConfCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterStarobinskyPotential
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

theorem BookProof.ScalaronDensitized.halfDensityUnitary_mem_densConfCore (x : physConfCore M alpha) :
    halfDensityUnitary (x : Lp ℂ 2 physMeasure) ∈ densConfCore M alpha := by sorry
