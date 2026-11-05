-- Prove2me | Theorems.Thm_BookProof_DegEnergy_integral_cx_sq_mul_normSq
-- name    : BookProof.DegEnergy.integral_cx_sq_mul_normSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:19:04.189411+00:00
-- url     : https://prove2.me/theorems/da4ef0a9-127f-45d9-9074-7cea3528efa0
-- title:
--   `BookProof.DegEnergy.integral_cx_sq_mul_normSq` {χ : Vd d → ℝ} (v : Vd d → ℂ) : ∀ x : Vd d, cx χ x ^ 2 * (starRingEnd ℂ) (v x) * v x = (((χ x) ^ 2 * ‖v x‖ ^ 2 : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDegEnergyEstimate`.
--
--   `BookProof.DegEnergy.integral_cx_sq_mul_normSq` {χ : Vd d → ℝ} (v : Vd d → ℂ) : ∀ x : Vd d, cx χ x ^ 2 * (starRingEnd ℂ) (v x) * v x = (((χ x) ^ 2 * ‖v x‖ ^ 2 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.DegEnergy.integral_cx_sq_mul_normSq`.

-- Generated from ChapterDegEnergyEstimate.lean — theorem BookProof.DegEnergy.integral_cx_sq_mul_normSq
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterConvolutionCalc
import Mathlib
import Definitions.Def_ChapterDegEnergyEstimate
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFockWeightedSchurEsa
open BookProof.HermiteProductCore
open BookProof.DegEnergy



open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger
open BookProof.ConvolutionCalc

noncomputable section

variable {d : ℕ}

variable (S : Finset (Fin d))

theorem BookProof.DegEnergy.integral_cx_sq_mul_normSq {χ : Vd d → ℝ} (v : Vd d → ℂ) :
    ∀ x : Vd d, cx χ x ^ 2 * (starRingEnd ℂ) (v x) * v x
      = (((χ x) ^ 2 * ‖v x‖ ^ 2 : ℝ) : ℂ) := by sorry
