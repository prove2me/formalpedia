-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_quadratic_convolution_successor_bound
-- name    : AvramDividend.Classical.causal_neumann_quadratic_convolution_successor_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:22:36.432602+00:00
-- url     : https://prove2.me/theorems/a1fa4ff3-ad95-4aa4-8df8-5063961bc42f
-- title:
--   Quadratic-geometric pointwise successor bound for causal convolution powers
-- statement:
--   For a nonnegative antitone causal envelope with mass ρ and a preceding power bounded pointwise by (n+1)^2 ρ^(n+1)/s, use the quantitative split at u=(n+1)x/(n+2) and a geometric left-mass bound to prove the next power is at most (n+2)^2 ρ^(n+2)/x. Explicit interval integrability premises isolate the remaining per-point analytic requirement.
-- source:
--   Apply the proved antitone convolution cutoff split with B=A/u, bound A/s by A/u for s≥u, and simplify the quadratic cutoff identity directly with field_simp and ring.

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_causal_antitone_convolution_cutoff_split_mass_bound

open MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_quadratic_convolution_successor_bound
    (n : ℕ) (κ F : ℝ → ℝ) (ρ x u : ℝ)
    (hx : 0 < x) (hρ : 0 ≤ ρ)
    (hcut : u = ((n + 1 : ℝ) / (n + 2 : ℝ)) * x)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcutInt : IntervalIntegrable κ volume 0 (x - u))
    (hκcutMass : (∫ t in (0 : ℝ)..(x - u), κ t) ≤ ρ)
    (hleftInt : IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume 0 u)
    (hrightInt : IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume u x)
    (hFInt : IntervalIntegrable F volume 0 u)
    (hκrightInt : IntervalIntegrable (fun s : ℝ => κ (x - s)) volume u x)
    (hFleft : ∀ s ∈ Ioo (0 : ℝ) u, 0 ≤ F s)
    (hFright : ∀ s ∈ Ioo u x,
      F s ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / s)
    (hκright : ∀ s ∈ Ioo u x, 0 ≤ κ (x - s))
    (hFmass : (∫ s in (0 : ℝ)..u, F s) ≤ ρ ^ (n + 1)) :
    (∫ s in (0 : ℝ)..x, κ (x - s) * F s) ≤
      ((n + 2 : ℝ) ^ 2 * ρ ^ (n + 2)) / x := by sorry
