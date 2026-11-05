-- Prove2me | Theorems.Thm_BookProof_ConvolutionCalc_dcoord_cnv
-- name    : BookProof.ConvolutionCalc.dcoord_cnv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:12:57.313802+00:00
-- url     : https://prove2.me/theorems/48f1a503-2455-4786-b784-0b08aee5149d
-- title:
--   `BookProof.ConvolutionCalc.dcoord_cnv` {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConvolutionCalc`.
--
--   `BookProof.ConvolutionCalc.dcoord_cnv` {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ) (j : Fin d) : dcoord j (cnv u ρ) = cnv u (dcoord j ρ)
--
--   Formalization note: Lean 4 identifier `BookProof.ConvolutionCalc.dcoord_cnv`.

-- Generated from ChapterConvolutionCalc.lean — theorem BookProof.ConvolutionCalc.dcoord_cnv
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Mathlib
import Definitions.Def_ChapterConvolutionCalc
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFockWeightedSchurEsa
open BookProof.HermiteProductCore
open BookProof.ConvolutionCalc



open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger

noncomputable section

variable {d : ℕ}

theorem BookProof.ConvolutionCalc.dcoord_cnv {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d)))
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ) (j : Fin d) :
    dcoord j (cnv u ρ) = cnv u (dcoord j ρ) := by sorry
