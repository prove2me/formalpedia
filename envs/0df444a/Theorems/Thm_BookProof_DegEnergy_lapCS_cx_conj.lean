-- Prove2me | Theorems.Thm_BookProof_DegEnergy_lapCS_cx_conj
-- name    : BookProof.DegEnergy.lapCS_cx_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:18:57.953068+00:00
-- url     : https://prove2.me/theorems/a6fa136f-fad4-4c72-ae09-56c957c9d42e
-- title:
--   `BookProof.DegEnergy.lapCS_cx_conj` {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (S : Finset (Fin d)) (y : Vd d) : (starRingEnd ℂ) (lapCS S (cx χ) y) = lapCS S...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDegEnergyEstimate`.
--
--   `BookProof.DegEnergy.lapCS_cx_conj` {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (S : Finset (Fin d)) (y : Vd d) : (starRingEnd ℂ) (lapCS S (cx χ) y) = lapCS S (cx χ) y
--
--   Formalization note: Lean 4 identifier `BookProof.DegEnergy.lapCS_cx_conj`.

-- Generated from ChapterDegEnergyEstimate.lean — theorem BookProof.DegEnergy.lapCS_cx_conj
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

theorem BookProof.DegEnergy.lapCS_cx_conj {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (S : Finset (Fin d)) (y : Vd d) :
    (starRingEnd ℂ) (lapCS S (cx χ) y) = lapCS S (cx χ) y := by sorry
