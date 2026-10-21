-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_preserves_order_and_bounds
-- name    : AvramDividend.Classical.levy_transition_preserves_order_and_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T16:34:45.009799+00:00
-- url     : https://prove2.me/theorems/e69039cf-da1c-4f8d-bb35-cfe7523a81a0
-- title:
--   The Lévy transition semigroup preserves monotonicity of states and deterministic payoff bounds
-- statement:
--   The given spectrally negative Lévy process has P a probability measure. For a monotone real Borel payoff f with uniform bounds a≤f(z)≤b and integrable shifted payoffs f(x+X_t), the transition operator P_t f(x)=E[f(x+X_t)] is monotone in x, and takes values in the same deterministic interval [a,b] for every x. Use pointwise preservation of order under translation and pinned integral_mono_ae, with integrable constants and total probability mass 1. This is a fundamental positivity/order-preservation and L∞ bound for extending finite simple-state conditional Markov results to general bounded random starting reserves. It does not establish strong continuity or the infinitesimal generator, which require dominated-convergence and Lévy-Khintchine analyses.
-- source:
--   Source-faithful Lévy transition semigroup using only the given X.isProbability and pinned MeasureTheory.integral_mono_ae, no Open dependencies.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_preserves_order_and_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (f : ℝ → ℝ) (hf : Monotone f)
    (a b : ℝ) (hbound : ∀ z, a ≤ f z ∧ f z ≤ b)
    (hInt : ∀ x : ℝ, Integrable (fun ω => f (x + X.X t ω)) P) :
    Monotone (fun x : ℝ => ∫ ω, f (x + X.X t ω) ∂P) ∧
    (∀ x : ℝ, a ≤ (∫ ω, f (x + X.X t ω) ∂P) ∧
      (∫ ω, f (x + X.X t ω) ∂P) ≤ b) := by sorry
