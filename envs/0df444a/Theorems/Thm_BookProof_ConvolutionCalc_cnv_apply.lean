-- Prove2me | Theorems.Thm_BookProof_ConvolutionCalc_cnv_apply
-- name    : BookProof.ConvolutionCalc.cnv_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:12:25.671193+00:00
-- url     : https://prove2.me/theorems/7f1f0d76-b926-45ec-8c64-7401d1badd69
-- title:
--   `BookProof.ConvolutionCalc.cnv_apply` (u ρ : Vd d → ℂ) (x : Vd d) : cnv u ρ x = ∫ y, u y * ρ (x - y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConvolutionCalc`.
--
--   `BookProof.ConvolutionCalc.cnv_apply` (u ρ : Vd d → ℂ) (x : Vd d) : cnv u ρ x = ∫ y, u y * ρ (x - y)
--
--   Formalization note: Lean 4 identifier `BookProof.ConvolutionCalc.cnv_apply`.

-- Generated from ChapterConvolutionCalc.lean — theorem BookProof.ConvolutionCalc.cnv_apply
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

theorem BookProof.ConvolutionCalc.cnv_apply (u ρ : Vd d → ℂ) (x : Vd d) : cnv u ρ x = ∫ y, u y * ρ (x - y) := by sorry
