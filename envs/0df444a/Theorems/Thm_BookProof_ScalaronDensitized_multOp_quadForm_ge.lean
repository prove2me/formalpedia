-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_multOp_quadForm_ge
-- name    : BookProof.ScalaronDensitized.multOp_quadForm_ge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:21:53.051167+00:00
-- url     : https://prove2.me/theorems/d625fbdf-1c72-4793-90c0-2840b841aa27
-- title:
--   `BookProof.ScalaronDensitized.multOp_quadForm_ge` (mu : Measure X) {g : X → ℝ} (hg : Measurable g) {c : ℝ} (hc : ∀ a, -c ≤ g a) (f : boundedEnergyCore mu g) : -c * ‖(f : Lp ℂ 2 mu)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.multOp_quadForm_ge` (mu : Measure X) {g : X → ℝ} (hg : Measurable g) {c : ℝ} (hc : ∀ a, -c ≤ g a) (f : boundedEnergyCore mu g) : -c * ‖(f : Lp ℂ 2 mu)‖ ^ 2 ≤ quadForm ((boundedEnergyCore mu g).subtype.comp (multOp mu hg)) f
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.multOp_quadForm_ge`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.multOp_quadForm_ge
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

theorem BookProof.ScalaronDensitized.multOp_quadForm_ge (mu : Measure X) {g : X → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : ∀ a, -c ≤ g a) (f : boundedEnergyCore mu g) :
    -c * ‖(f : Lp ℂ 2 mu)‖ ^ 2
      ≤ quadForm ((boundedEnergyCore mu g).subtype.comp (multOp mu hg)) f := by sorry
