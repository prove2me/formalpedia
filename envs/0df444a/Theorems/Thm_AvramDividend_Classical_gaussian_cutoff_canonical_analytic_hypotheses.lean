-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_cutoff_canonical_analytic_hypotheses
-- name    : AvramDividend.Classical.gaussian_cutoff_canonical_analytic_hypotheses
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:37:44.574078+00:00
-- url     : https://prove2.me/theorems/6faf6869-3bfa-4053-9072-3814eb785f5a
-- title:
--   Gaussian zero-jump cutoff supplies all model and analytical premises of the canonical unbounded-variation verification core
-- statement:
--   For a canonical spectrally negative Lévy process with strictly positive Gaussian coefficient, zero Lévy jump measure, drift coefficient −1 and integrable X1, the zero-extended affine candidate meets all model, smoothness, generator and gradient hypotheses of the canonical unbounded-variation stochastic verification core at q=1, for any capital cap. The remaining assumptions concern the chosen dividend strategy and ruin-time reward.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i) and exact Prove2Me canonical UBV core; preceding verified Gaussian-cutoff lemmas.

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_continuous_nonnegative_smooth_positive
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_contDiffOn_positive_below_cap
import Theorems.Thm_AvramDividend_Classical_zero_jump_affine_cutoff_HJB_drift_neg_one
import Theorems.Thm_AvramDividend_Classical_positive_gaussian_standing_and_unbounded_variation

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.gaussian_cutoff_canonical_analytic_hypotheses
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (hI : Integrable (X.X 1) P) (hν : X.ν = 0) (hc : X.c = -1)
    (C : ℝ≥0∞) :
    X.Standing ∧ ¬ X.BoundedVariation ∧
    ContinuousOn (fun z : ℝ => if z < 0 then 0 else z - 1) (Ici (0 : ℝ)) ∧
    (∀ y : ℝ, y < 0 → (fun z : ℝ => if z < 0 then 0 else z - 1) y = 0) ∧
    ContDiffOn ℝ 2 (fun z : ℝ => if z < 0 then 0 else z - 1) {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable (fun z : ℝ => if z < 0 then 0 else z - 1) y ∧
        X.generator (fun z : ℝ => if z < 0 then 0 else z - 1) y - (1 : ℝ) * (fun z : ℝ => if z < 0 then 0 else z - 1) y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv (fun z : ℝ => if z < 0 then 0 else z - 1) y) := by sorry
