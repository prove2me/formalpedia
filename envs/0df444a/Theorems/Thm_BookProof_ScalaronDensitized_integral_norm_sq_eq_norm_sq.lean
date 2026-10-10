-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_integral_norm_sq_eq_norm_sq
-- name    : BookProof.ScalaronDensitized.integral_norm_sq_eq_norm_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:21:45.162175+00:00
-- url     : https://prove2.me/theorems/738161b9-a6d7-430b-88fd-0492eba483bd
-- title:
--   `BookProof.ScalaronDensitized.integral_norm_sq_eq_norm_sq` (mu : Measure X) (f : Lp ℂ 2 mu) : ∫ a, ‖(f : X → ℂ) a‖ ^ 2 ∂mu = ‖f‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.integral_norm_sq_eq_norm_sq` (mu : Measure X) (f : Lp ℂ 2 mu) : ∫ a, ‖(f : X → ℂ) a‖ ^ 2 ∂mu = ‖f‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.integral_norm_sq_eq_norm_sq`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.integral_norm_sq_eq_norm_sq
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
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

theorem BookProof.ScalaronDensitized.integral_norm_sq_eq_norm_sq (mu : Measure X) (f : Lp ℂ 2 mu) :
    ∫ a, ‖(f : X → ℂ) a‖ ^ 2 ∂mu = ‖f‖ ^ 2 := by sorry
