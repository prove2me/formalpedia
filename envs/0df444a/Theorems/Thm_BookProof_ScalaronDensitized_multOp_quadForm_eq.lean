-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_multOp_quadForm_eq
-- name    : BookProof.ScalaronDensitized.multOp_quadForm_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T22:58:39.407995+00:00
-- url     : https://prove2.me/theorems/027a5f24-7d8f-405c-b148-38c904f8841e
-- title:
--   `BookProof.ScalaronDensitized.multOp_quadForm_eq` (mu : Measure X) {g : X → ℝ} (hg : Measurable g) (f : boundedEnergyCore mu g) : quadForm ((boundedEnergyCore mu g).subtype.comp (m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.multOp_quadForm_eq` (mu : Measure X) {g : X → ℝ} (hg : Measurable g) (f : boundedEnergyCore mu g) : quadForm ((boundedEnergyCore mu g).subtype.comp (multOp mu hg)) f = ∫ a, g a * ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2 ∂mu
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.multOp_quadForm_eq`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.multOp_quadForm_eq
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFockContinuum
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.ScalaronDensitized



open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)
variable {X : Type*} [MeasurableSpace X]

theorem BookProof.ScalaronDensitized.multOp_quadForm_eq (mu : Measure X) {g : X → ℝ} (hg : Measurable g)
    (f : boundedEnergyCore mu g) :
    quadForm ((boundedEnergyCore mu g).subtype.comp (multOp mu hg)) f
      = ∫ a, g a * ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2 ∂mu := by sorry
