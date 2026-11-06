-- Prove2me | Theorems.Thm_BookProof_DegEnergy_norm_cx
-- name    : BookProof.DegEnergy.norm_cx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T16:00:14.368969+00:00
-- url     : https://prove2.me/theorems/109123da-3c2a-4d31-be91-dd0910fb5e0d
-- title:
--   `BookProof.DegEnergy.norm_cx` (χ : Vd d → ℝ) (x : Vd d) : ‖cx χ x‖ = |χ x| := by simp [cx] /-- The partial Laplacian of a real-valued function is real. -/ theorem lapCS_cx_conj {χ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDegEnergyEstimate`.
--
--   `BookProof.DegEnergy.norm_cx` (χ : Vd d → ℝ) (x : Vd d) : ‖cx χ x‖ = |χ x| := by simp [cx] /-- The partial Laplacian of a real-valued function is real. -/ theorem lapCS_cx_conj {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (S : Finset (Fin d)) (y : Vd d) : (starRingEnd ℂ) (lapCS S (cx χ) y) = lapCS S (cx χ) y
--
--   Formalization note: Lean 4 identifier `BookProof.DegEnergy.norm_cx`.

-- Generated from ChapterDegEnergyEstimate.lean — theorem BookProof.DegEnergy.norm_cx
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

theorem BookProof.DegEnergy.norm_cx (χ : Vd d → ℝ) (x : Vd d) : ‖cx χ x‖ = |χ x| := by sorry
