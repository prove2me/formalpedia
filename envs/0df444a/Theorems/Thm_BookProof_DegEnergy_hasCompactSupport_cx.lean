-- Prove2me | Theorems.Thm_BookProof_DegEnergy_hasCompactSupport_cx
-- name    : BookProof.DegEnergy.hasCompactSupport_cx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:19:05.213208+00:00
-- url     : https://prove2.me/theorems/5b03ec08-1cb3-4eac-8ac4-f5d822aa2dd3
-- title:
--   `BookProof.DegEnergy.hasCompactSupport_cx` {χ : Vd d → ℝ} (hχc : HasCompactSupport χ) : HasCompactSupport (cx χ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDegEnergyEstimate`.
--
--   `BookProof.DegEnergy.hasCompactSupport_cx` {χ : Vd d → ℝ} (hχc : HasCompactSupport χ) : HasCompactSupport (cx χ)
--
--   Formalization note: Lean 4 identifier `BookProof.DegEnergy.hasCompactSupport_cx`.

-- Generated from ChapterDegEnergyEstimate.lean — theorem BookProof.DegEnergy.hasCompactSupport_cx
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterConvolutionCalc
import Mathlib
import Definitions.Def_ChapterDegEnergyEstimate
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.DegEnergy



open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger
open BookProof.ConvolutionCalc

noncomputable section

variable {d : ℕ}

variable (S : Finset (Fin d))

theorem BookProof.DegEnergy.hasCompactSupport_cx {χ : Vd d → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (cx χ) := by sorry
