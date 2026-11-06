-- Prove2me | Theorems.Thm_BookProof_DegEnergy_energy_bound
-- name    : BookProof.DegEnergy.energy_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:19:10.404206+00:00
-- url     : https://prove2.me/theorems/23f52b60-716b-4b01-a039-c8feffa89e7f
-- title:
--   `BookProof.DegEnergy.energy_bound` {z : ℂ} (hz : z.re = 0) {v G : Vd d → ℂ} (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (hG : Continuous G) (hid : ∀ x, lapCS S v x = G x - z * v x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDegEnergyEstimate`.
--
--   `BookProof.DegEnergy.energy_bound` {z : ℂ} (hz : z.re = 0) {v G : Vd d → ℂ} (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (hG : Continuous G) (hid : ∀ x, lapCS S v x = G x - z * v x) {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ) : (∫ x, cx χ x ^ 2 * (starRingEnd ℂ) (v x) * G x).re ≤ 2 * ∑ j ∈ S, ∫ x, ‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.DegEnergy.energy_bound`.

-- Generated from ChapterDegEnergyEstimate.lean — theorem BookProof.DegEnergy.energy_bound
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

theorem BookProof.DegEnergy.energy_bound {z : ℂ} (hz : z.re = 0) {v G : Vd d → ℂ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (hG : Continuous G)
    (hid : ∀ x, lapCS S v x = G x - z * v x)
    {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ) :
    (∫ x, cx χ x ^ 2 * (starRingEnd ℂ) (v x) * G x).re
      ≤ 2 * ∑ j ∈ S, ∫ x, ‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2 := by sorry
