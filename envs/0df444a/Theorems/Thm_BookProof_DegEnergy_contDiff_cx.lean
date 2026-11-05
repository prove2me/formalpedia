-- Prove2me | Theorems.Thm_BookProof_DegEnergy_contDiff_cx
-- name    : BookProof.DegEnergy.contDiff_cx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:20:01.951922+00:00
-- url     : https://prove2.me/theorems/b1c9a1d6-ec1b-4ef1-a257-cd96a7c13e94
-- title:
--   `BookProof.DegEnergy.contDiff_cx` {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cx χ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDegEnergyEstimate`.
--
--   `BookProof.DegEnergy.contDiff_cx` {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cx χ)
--
--   Formalization note: Lean 4 identifier `BookProof.DegEnergy.contDiff_cx`.

-- Generated from ChapterDegEnergyEstimate.lean — theorem BookProof.DegEnergy.contDiff_cx
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

theorem BookProof.DegEnergy.contDiff_cx {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cx χ) := by sorry
