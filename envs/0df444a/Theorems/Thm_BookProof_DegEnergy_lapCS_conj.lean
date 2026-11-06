-- Prove2me | Theorems.Thm_BookProof_DegEnergy_lapCS_conj
-- name    : BookProof.DegEnergy.lapCS_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:18:50.670061+00:00
-- url     : https://prove2.me/theorems/a35632f2-4725-41b2-87ff-5a09441e4f12
-- title:
--   `BookProof.DegEnergy.lapCS_conj` {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (S : Finset (Fin d)) (y : Vd d) : (starRingEnd ℂ) (lapCS S g y) = lapCS S (fun t => (sta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDegEnergyEstimate`.
--
--   `BookProof.DegEnergy.lapCS_conj` {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (S : Finset (Fin d)) (y : Vd d) : (starRingEnd ℂ) (lapCS S g y) = lapCS S (fun t => (starRingEnd ℂ) (g t)) y
--
--   Formalization note: Lean 4 identifier `BookProof.DegEnergy.lapCS_conj`.

-- Generated from ChapterDegEnergyEstimate.lean — theorem BookProof.DegEnergy.lapCS_conj
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

theorem BookProof.DegEnergy.lapCS_conj {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (S : Finset (Fin d)) (y : Vd d) :
    (starRingEnd ℂ) (lapCS S g y) = lapCS S (fun t => (starRingEnd ℂ) (g t)) y := by sorry
