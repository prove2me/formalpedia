-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_halfDensityUnitary_densConfCore_surjective
-- name    : BookProof.ScalaronDensitized.halfDensityUnitary_densConfCore_surjective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:21:16.068418+00:00
-- url     : https://prove2.me/theorems/c256322a-d8fe-4a5e-87de-f8555298c61a
-- title:
--   `BookProof.ScalaronDensitized.halfDensityUnitary_densConfCore_surjective` (h : densConfCore M alpha) : ∃ x : physConfCore M alpha, halfDensityUnitary (x : Lp ℂ 2 physMeasure) = (h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.halfDensityUnitary_densConfCore_surjective` (h : densConfCore M alpha) : ∃ x : physConfCore M alpha, halfDensityUnitary (x : Lp ℂ 2 physMeasure) = (h : Lp ℂ 2 qgSrcMeasure)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.halfDensityUnitary_densConfCore_surjective`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.halfDensityUnitary_densConfCore_surjective
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

theorem BookProof.ScalaronDensitized.halfDensityUnitary_densConfCore_surjective (h : densConfCore M alpha) :
    ∃ x : physConfCore M alpha,
      halfDensityUnitary (x : Lp ℂ 2 physMeasure) = (h : Lp ℂ 2 qgSrcMeasure) := by sorry
