-- Prove2me | Theorems.Thm_BookProof_DegEnergy_integrable_of_cc
-- name    : BookProof.DegEnergy.integrable_of_cc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:29:29.911729+00:00
-- url     : https://prove2.me/theorems/f822d6c0-06e7-4e7d-98b7-4f5e9e32f201
-- title:
--   `BookProof.DegEnergy.integrable_of_cc` {f : Vd d → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) : Integrable f (volume : Measure (Vd d))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDegEnergyEstimate`.
--
--   `BookProof.DegEnergy.integrable_of_cc` {f : Vd d → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) : Integrable f (volume : Measure (Vd d))
--
--   Formalization note: Lean 4 identifier `BookProof.DegEnergy.integrable_of_cc`.

-- Generated from ChapterDegEnergyEstimate.lean — theorem BookProof.DegEnergy.integrable_of_cc
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

theorem BookProof.DegEnergy.integrable_of_cc {f : Vd d → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (volume : Measure (Vd d)) := by sorry
