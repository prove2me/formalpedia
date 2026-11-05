-- Prove2me | Theorems.Thm_BookProof_DegEnergy_dcoord_conj
-- name    : BookProof.DegEnergy.dcoord_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:18:41.986683+00:00
-- url     : https://prove2.me/theorems/d821351d-f9dc-4947-8bc6-ba608404e7b9
-- title:
--   `BookProof.DegEnergy.dcoord_conj` {v : Vd d → ℂ} (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (j : Fin d) (x : Vd d) : dcoord j (fun y => (starRingEnd ℂ) (v y)) x = (starRingEnd ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDegEnergyEstimate`.
--
--   `BookProof.DegEnergy.dcoord_conj` {v : Vd d → ℂ} (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (j : Fin d) (x : Vd d) : dcoord j (fun y => (starRingEnd ℂ) (v y)) x = (starRingEnd ℂ) (dcoord j v x)
--
--   Formalization note: Lean 4 identifier `BookProof.DegEnergy.dcoord_conj`.

-- Generated from ChapterDegEnergyEstimate.lean — theorem BookProof.DegEnergy.dcoord_conj
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

theorem BookProof.DegEnergy.dcoord_conj {v : Vd d → ℂ} (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (j : Fin d)
    (x : Vd d) :
    dcoord j (fun y => (starRingEnd ℂ) (v y)) x = (starRingEnd ℂ) (dcoord j v x) := by sorry
