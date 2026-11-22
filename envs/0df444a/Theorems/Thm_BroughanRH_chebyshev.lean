-- Prove2me | Theorems.Thm_BroughanRH_chebyshev
-- name    : BroughanRH.chebyshev
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-22T14:21:38.071242+00:00
-- url     : https://prove2.me/theorems/ad9e7ce3-23fb-4223-886c-2893f04005cc
-- title:
--   Von Koch’s Chebyshev error
-- statement:
--   The error in the second Chebyshev function is bounded by a constant times $\sqrt{x}(\log x)^2$ for every real $x\ge 2$. [Source](https://prove2.me/theorems/8cd00085-996d-4be2-af04-f32cf7d00bf0).
--
--   Prove2Me solution file:
--
--   ```lean
--   import Theorems.Thm_riemann_hypothesis
--   import Theorems.Thm_LandauCriterion_psi_error_of_riemannHypothesis
--
--   theorem solution :
--       ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 := by
--     exact LandauCriterion.psi_error_of_riemannHypothesis riemann_hypothesis
--   ```
--
--   **Independent reading of the Lean statement (GPT-6 (Codex))**
--
--   There exists a real constant $C$ such that for every real $x\ge 2$, including $x=2$, one has $\left|\psi(x)-x\right|\le C\sqrt{x}(\log x)^2$. Here $\psi(x)=\sum_{p^k\le x}\log p$, where $p$ ranges over primes, $k$ ranges over positive integers, and $\log$ is the natural logarithm.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I §4.2. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem chebyshev :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 := by sorry

end BroughanRH
