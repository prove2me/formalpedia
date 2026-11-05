-- Prove2me | Theorems.Thm_BookProof_ConvolutionCalc_contDiff_cnv
-- name    : BookProof.ConvolutionCalc.contDiff_cnv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:12:53.849254+00:00
-- url     : https://prove2.me/theorems/cc842b04-fc85-4898-b6c5-3bccb09658b5
-- title:
--   `BookProof.ConvolutionCalc.contDiff_cnv` {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConvolutionCalc`.
--
--   `BookProof.ConvolutionCalc.contDiff_cnv` {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cnv u ρ)
--
--   Formalization note: Lean 4 identifier `BookProof.ConvolutionCalc.contDiff_cnv`.

-- Generated from ChapterConvolutionCalc.lean — theorem BookProof.ConvolutionCalc.contDiff_cnv
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

theorem BookProof.ConvolutionCalc.contDiff_cnv {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d)))
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cnv u ρ) := by sorry
