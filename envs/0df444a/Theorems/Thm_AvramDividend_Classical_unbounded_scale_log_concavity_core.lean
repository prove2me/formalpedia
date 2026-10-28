-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_log_concavity_core
-- name    : AvramDividend.Classical.unbounded_scale_log_concavity_core
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T07:05:30.108008+00:00
-- url     : https://prove2.me/theorems/bb6ee1d8-2f9f-4fad-b81f-f24bdb3081fd
-- title:
--   Log-concavity of the q-scale function for unbounded-variation spectrally negative Lévy processes
-- statement:
--   Corrected publication request after a 24 October 2026 formal-statement compiler failure on the set and function binder. This core is an independent missing fluctuation-theory theorem for Avram's root-connected Open unbounded_tilted_scale_log_concavity (0aa170e8-3557-48df-893e-a2015627238e). The Proved scaleFunction_strict_pos_of_unbounded_variation and esscher_tilted_log_concave_of_scale_log_concave transfer log-concavity of log W to that parent via log(exp(-φx)W(x)) = log W(x) - φx. Proving this core requires a genuine excursion-height or Wiener-Hopf representation, without assuming Standing and without importing its parent. The corrected statement writes the domain as Set.Ioi and explicitly types the lambda binder to avoid an authoring elaboration ambiguity.
-- source:
--   Avram, Palmowski and Pistorius (2007); scale-function fluctuation-theoretic log-concavity.

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_log_concavity_core
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => Real.log (W x)) := by sorry
