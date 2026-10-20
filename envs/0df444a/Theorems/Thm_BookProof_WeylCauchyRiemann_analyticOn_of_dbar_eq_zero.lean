-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_analyticOn_of_dbar_eq_zero
-- name    : BookProof.WeylCauchyRiemann.analyticOn_of_dbar_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:19:45.061006+00:00
-- url     : https://prove2.me/theorems/67edb435-b411-4830-813a-1bc8d4c7b9f7
-- title:
--   `BookProof.WeylCauchyRiemann.analyticOn_of_dbar_eq_zero` {g : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hg : ∀ z ∈ s, DifferentiableAt ℝ g z) (hdbar : ∀ z ∈ s, dbar g z = 0) : AnalyticOn
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.analyticOn_of_dbar_eq_zero` {g : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hg : ∀ z ∈ s, DifferentiableAt ℝ g z) (hdbar : ∀ z ∈ s, dbar g z = 0) : AnalyticOn ℂ g s
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.analyticOn_of_dbar_eq_zero`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.analyticOn_of_dbar_eq_zero
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.analyticOn_of_dbar_eq_zero {g : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s)
    (hg : ∀ z ∈ s, DifferentiableAt ℝ g z) (hdbar : ∀ z ∈ s, dbar g z = 0) :
    AnalyticOn ℂ g s := by sorry
