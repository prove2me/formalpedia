-- Prove2me | Theorems.Thm_BookProof_DegEnergy_integral_dcoord_mul
-- name    : BookProof.DegEnergy.integral_dcoord_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:18:51.162948+00:00
-- url     : https://prove2.me/theorems/5b7a4d26-c95c-4abf-9caa-696fe738d16e
-- title:
--   `BookProof.DegEnergy.integral_dcoord_mul` {f g : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDegEnergyEstimate`.
--
--   `BookProof.DegEnergy.integral_dcoord_mul` {f g : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (j : Fin d) : ∫ x, f x * dcoord j g x = -∫ x, dcoord j f x * g x
--
--   Formalization note: Lean 4 identifier `BookProof.DegEnergy.integral_dcoord_mul`.

-- Generated from ChapterDegEnergyEstimate.lean — theorem BookProof.DegEnergy.integral_dcoord_mul
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

theorem BookProof.DegEnergy.integral_dcoord_mul {f g : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (j : Fin d) :
    ∫ x, f x * dcoord j g x = -∫ x, dcoord j f x * g x := by sorry
