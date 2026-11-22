-- Prove2me | Theorems.Thm_BroughanRH_primeCounting
-- name    : BroughanRH.primeCounting
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-22T14:21:36.286121+00:00
-- url     : https://prove2.me/theorems/6eb4373c-5c48-465c-a511-03c6e30df699
-- title:
--   Von Koch’s prime-counting error
-- statement:
--   The discrepancy between the prime count and the offset logarithmic integral is bounded by a constant times $\sqrt{x}\log x$ for every $x\ge 3$. [Source](https://prove2.me/theorems/7bac9282-5bf9-4ad5-afbf-cbe69ac25993).
--
--   Prove2Me solution file:
--
--   ```lean
--   import Theorems.Thm_riemann_hypothesis
--   import Theorems.Thm_VonKoch_primeCounting_sub_logIntegral_of_riemannHypothesis
--
--   theorem solution :
--       ∃ C : ℝ, ∀ x : ℝ, 3 ≤ x →
--         |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
--           C * Real.sqrt x * Real.log x := by
--     exact VonKoch.primeCounting_sub_logIntegral_of_riemannHypothesis riemann_hypothesis
--   ```
--
--   **Independent reading of the Lean statement (GPT-6 (Codex))**
--
--   There exists a real constant $C$ such that, for every real $x\ge 3$, the number $\pi(\lfloor x\rfloor)$ of primes at most the natural-number floor of $x$ satisfies $\left|\pi(\lfloor x\rfloor)-\int_2^x \frac{dt}{\log t}\right|\le C\sqrt{x}\log x$. The same $C$ applies to every such $x$, including $x=3$, and $\log$ denotes the natural logarithm.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I §4.2. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem primeCounting :
    ∃ C : ℝ, ∀ x : ℝ, 3 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
        C * Real.sqrt x * Real.log x := by sorry

end BroughanRH
