-- Prove2me | Theorems.Thm_BookProof_ConvolutionCalc_hasCompactSupport_dcoord
-- name    : BookProof.ConvolutionCalc.hasCompactSupport_dcoord
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:11:56.062727+00:00
-- url     : https://prove2.me/theorems/97b54fc5-82c1-451d-b71e-604dce77cbdb
-- title:
--   `BookProof.ConvolutionCalc.hasCompactSupport_dcoord` {ρ : Vd d → ℂ} (hc : HasCompactSupport ρ) (j : Fin d) : HasCompactSupport (dcoord j ρ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConvolutionCalc`.
--
--   `BookProof.ConvolutionCalc.hasCompactSupport_dcoord` {ρ : Vd d → ℂ} (hc : HasCompactSupport ρ) (j : Fin d) : HasCompactSupport (dcoord j ρ)
--
--   Formalization note: Lean 4 identifier `BookProof.ConvolutionCalc.hasCompactSupport_dcoord`.

-- Generated from ChapterConvolutionCalc.lean — theorem BookProof.ConvolutionCalc.hasCompactSupport_dcoord
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

theorem BookProof.ConvolutionCalc.hasCompactSupport_dcoord {ρ : Vd d → ℂ}
    (hc : HasCompactSupport ρ) (j : Fin d) : HasCompactSupport (dcoord j ρ) := by sorry
