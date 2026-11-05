-- Prove2me | Theorems.Thm_BookProof_ConvolutionCalc_lapCS_cnv
-- name    : BookProof.ConvolutionCalc.lapCS_cnv
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T09:12:49.336597+00:00
-- url     : https://prove2.me/theorems/e06c4e63-3d4b-47d6-8fb7-b877d2272951
-- title:
--   `BookProof.ConvolutionCalc.lapCS_cnv` {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ) (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConvolutionCalc`.
--
--   `BookProof.ConvolutionCalc.lapCS_cnv` {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ) (S : Finset (Fin d)) (x : Vd d) : lapCS S (cnv u ρ) x = cnv u (lapCS S ρ) x
--
--   Formalization note: Lean 4 identifier `BookProof.ConvolutionCalc.lapCS_cnv`.

-- Generated from ChapterConvolutionCalc.lean — theorem BookProof.ConvolutionCalc.lapCS_cnv
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Mathlib
import Definitions.Def_ChapterConvolutionCalc
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.ConvolutionCalc



open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger

noncomputable section

variable {d : ℕ}

theorem BookProof.ConvolutionCalc.lapCS_cnv {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d)))
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ)
    (S : Finset (Fin d)) (x : Vd d) :
    lapCS S (cnv u ρ) x = cnv u (lapCS S ρ) x := by sorry
