-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_generating_cost_bound
-- name    : CountingLLL.ContractedWalk.generating_cost_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:48:08.188593+00:00
-- url     : https://prove2.me/theorems/2bedcd55-09cc-4a3a-a455-9039502e3347
-- title:
--   Contracted-walk generating-function cost integral bound
-- statement:
--   Let $G(z)$ be the generating function for upward changes of the paper’s contracted walk started from level one. For $0\leq\theta\leq9/40$, its cost-analysis integral satisfies $$\int_0^1\frac{z(1+G(z)+G(z)^2)}{1-\theta z(1+G(z)+G(z)^2)}\,dz<\frac{74}{25}.$$ Establishing that the weighted-change expectation $M$ equals this integral is a separate probabilistic step.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk
open scoped Interval

theorem CountingLLL.ContractedWalk.generating_cost_bound (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 9/40) :
    (∫ z in (0:ℝ)..1, z*(1+generatingFunction θ z+(generatingFunction θ z)^2)/
      (1-θ*z*(1+generatingFunction θ z+(generatingFunction θ z)^2))) < (74/25:ℝ) := by sorry
