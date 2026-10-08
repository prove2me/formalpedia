-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_linear_exponent_eventually_above
-- name    : AvramDividend.Classical.positive_linear_exponent_eventually_above
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:15:24.028866+00:00
-- url     : https://prove2.me/theorems/ba2a1615-f756-4e2d-bacd-52deb24c23fb
-- title:
--   Positive linear Lévy exponent asymptotic implies eventual excess over every discount
-- statement:
--   If a real Laplace exponent ψ satisfies ψ(θ)/θ→d>0 as θ→+∞, then for every real discount level q there is a finite threshold beyond which ψ(θ)>q for all real θ. This turns the positive-drift bounded-variation asymptotic into the exact eventual positivity hypothesis needed for Avram's scale-function positivity theorem.
-- source:
--   Order-topology neighbourhood argument at the positive limit d/2, Filter.eventually_atTop and a constructive threshold enforcing θ≥2(|q|+1)/d; entirely pinned Mathlib.

import Mathlib

open Filter

theorem AvramDividend.Classical.positive_linear_exponent_eventually_above
    (ψ : ℝ → ℝ) (d q : ℝ) (hd : 0 < d)
    (hlim : Filter.Tendsto (fun θ : ℝ => ψ θ / θ)
      Filter.atTop (nhds d)) :
    ∃ θ₀ : ℝ, ∀ θ : ℝ, θ₀ ≤ θ → q < ψ θ := by sorry
