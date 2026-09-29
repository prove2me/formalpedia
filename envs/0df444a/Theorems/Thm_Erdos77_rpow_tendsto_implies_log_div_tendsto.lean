-- Prove2me | Theorems.Thm_Erdos77_rpow_tendsto_implies_log_div_tendsto
-- name    : Erdos77.rpow_tendsto_implies_log_div_tendsto
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-26T22:47:55.839486+00:00
-- url     : https://prove2.me/theorems/cc42447f-e06f-46da-b744-e299dd051a38
-- title:
--   From root convergence to normalized log convergence
-- statement:
--   Let $a : \mathbb{N} \to \mathbb{R}$ be a real sequence that is eventually at least $1$, and suppose the normalized roots $a(k)^{1/k}$ converge to a positive real limit $L$:
--
--   $$
--   a(k)^{1/k} \to L, \qquad L > 0.
--   $$
--
--   Then the normalized logarithms $\log a(k)/k$ converge to a real limit (namely $\log L$).
--
--   This is the standard bridge between exponential-growth-rate limits and their logarithmic form: since $\log$ is continuous at the positive limit $L$, convergence of $a(k)^{1/k}$ gives convergence of $\log(a(k)^{1/k})$, and $\log(a(k)^{1/k}) = \log a(k)/k$ for large $k$ by eventual positivity of the terms. It isolates the pure-analysis content of passing between the root limit in Erd\H{o}s Problem 77 and the logarithmic growth-rate limit.
--
--   **Formalization Note** Lean's real power with exponent $1/k$ at $k = 0$ and the division by $(k : \mathbb{R})$ at $k = 0$ are both defined (junk) values; the conclusion only concerns the limit at infinity, so these single terms are irrelevant.
-- source:
--   Real analysis bridge between exponential growth-rate limits and logarithmic growth-rate limits, via continuity of the logarithm at positive points (cf. Rudin, Principles of Mathematical Analysis, Theorem 4.19) and the logarithm-of-power identity; Lean form via Mathlib `Real.continuousAt_log` and `Real.log_rpow`. Motivated by Erdos Problem #77, https://www.erdosproblems.com/77.

import Mathlib
open Filter Topology

namespace Erdos77
theorem rpow_tendsto_implies_log_div_tendsto (a : Nat → Real) (L : Real)
    (ha : ∀ᶠ k : Nat in Filter.atTop, 1 <= a k)
    (hL : Filter.Tendsto (fun k : Nat => (a k) ^ ((1 : Real) / (k : Real))) Filter.atTop (nhds L))
    (hLpos : 0 < L) :
    Exists fun l : Real => Filter.Tendsto (fun k : Nat => Real.log (a k) / (k : Real)) Filter.atTop (nhds l) := by sorry
end Erdos77
