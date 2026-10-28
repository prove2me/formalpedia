-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_incrementVector_law_implies_zeroBasedGrid_law
-- name    : AvramDividend.Classical.cross_levy_incrementVector_law_implies_zeroBasedGrid_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:41:23.426653+00:00
-- url     : https://prove2.me/theorems/1e55334a-9d13-41fa-9747-ea9a200b39a7
-- title:
--   Finite consecutive Lévy increment vector laws determine path-value vector laws across different probability spaces
-- statement:
--   For two spectrally negative Lévy processes on entirely different probability spaces, suppose their finite consecutive increment vectors on a common time grid starting at zero have equal pushforward laws. Then their finite vectors of observed Lévy path levels have exactly the same joint law. The deterministic measurable prefix-sum transformation and pathwise telescoping of consecutive increments reconstruct every path level. This extends already Proved same-space finite-grid stationarity to the cross-space identification required to transfer laws from the canonical Poisson model.
-- source:
--   Source-adapted from accepted levy_incrementVector_law_implies_gridPositions_law [29b795fb-d20a-4b93-a32d-21561b86c556], Proved all-n telescoping [cfe8b73d-6030-450c-b51b-8dadac274476], zero-start axiom. Direct cross-space bridge after Proved cross_levy_prefix_increment_rectangles_of_marginal_laws [e86abd7d-f2cd-4d23-bebb-f9d651e901a5].

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_all_n_levy_increment_telescoping

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.cross_levy_incrementVector_law_implies_zeroBasedGrid_law
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (t : ℕ → ℝ≥0) (ht0 : t 0 = 0) (n : ℕ)
    (hInc :
      Measure.map (fun ω : Ω₁ => fun i : Fin n =>
        X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P₁ =
      Measure.map (fun ω : Ω₂ => fun i : Fin n =>
        Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω) P₂) :
    Measure.map (fun ω : Ω₁ => fun i : Fin n =>
      X.X (t (i.val + 1)) ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun i : Fin n =>
      Y.X (t (i.val + 1)) ω) P₂ := by sorry
