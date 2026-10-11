-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_weakCauchyRiemannOn_of_analyticOn
-- name    : BookProof.WeylCauchyRiemann.weakCauchyRiemannOn_of_analyticOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:35:34.193091+00:00
-- url     : https://prove2.me/theorems/16c893e4-e145-4457-8f9d-445752cb58c8
-- title:
--   `BookProof.WeylCauchyRiemann.weakCauchyRiemannOn_of_analyticOn` {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : AnalyticOn ℂ g U) : WeakCauchyRiemannOn g U
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.weakCauchyRiemannOn_of_analyticOn` {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : AnalyticOn ℂ g U) : WeakCauchyRiemannOn g U
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.weakCauchyRiemannOn_of_analyticOn`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.weakCauchyRiemannOn_of_analyticOn
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.weakCauchyRiemannOn_of_analyticOn {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOn ℂ g U) : WeakCauchyRiemannOn g U := by sorry
