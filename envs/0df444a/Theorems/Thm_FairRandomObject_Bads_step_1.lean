-- Prove2me | Theorems.Thm_FairRandomObject_Bads_step_1
-- name    : FairRandomObject.Bads.step_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:38.206299+00:00
-- url     : https://prove2.me/theorems/2fdb81a8-5981-4653-ac06-5e4c0c58e33a
-- title:
--   Step 1, p. 25 — 1/n + θ/(n−1)(x̄/x_i − 1) ≥ 0 and its sum over N is ≥ 1, strictly off the diagonal for θ ≠ 0
-- statement:
--   Let $n\ge2$, $\theta\in[0,1]$, and let $x$ be a profile with $x_i>0$ for all $i$. Write $\psi^\theta_i(x)=\frac1n+\frac{\theta}{n-1}\big(\frac{\bar x}{x_i}-1\big)$. Then
--
--   1. $\psi^\theta_i(x)\ge0$ for every $i$;
--   2. $\displaystyle\sum_{i\in N}\psi^\theta_i(x)\ge1$;
--   3. if $\theta\ne0$ and $x$ is not parallel to $e^N$ (its coordinates are not all equal), the inequality in 2 is strict.
--
--   These facts make the Bottom-Heavy family (13) well defined: the shares are non-negative and the prefix sums eventually exceed $1$.
-- source:
--   Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 25, proof of Theorem 17, Step 1

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting
import Definitions.Def_FairRandomObject_Bads_BottomHeavy

namespace FairRandomObject.Bads

/-- Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 25, Step 1 of the proof of Theorem 17: for `θ ∈ [0, 1]` and a profile
with all `x_i > 0`, each `1/n + θ/(n−1)(x̄/x_i − 1)` is non-negative and their sum over `N` is
at least `1`, strictly if `x` is not parallel to `e^N` and `θ ≠ 0`. This is why (13) is well
defined.

**Formalization Note.** "Parallel to `e^N`" is "all coordinates equal". The positivity
`x_i > 0` is required since `x̄/x_i` is undefined (the paper's `+∞`) at `x_i = 0`. -/
theorem step_1 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    (∀ i, 0 ≤ psi n θ x i) ∧ 1 ≤ ∑ i, psi n θ x i ∧
      (θ ≠ 0 → (¬ ∃ c : ℝ, ∀ i, x i = c) → 1 < ∑ i, psi n θ x i) := by sorry

end FairRandomObject.Bads
