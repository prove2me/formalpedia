-- Prove2me | Theorems.Thm_BroughanRH_landau
-- name    : BroughanRH.landau
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-22T14:21:45.486739+00:00
-- url     : https://prove2.me/theorems/d6ee40e8-4731-4348-bec6-5dd4530c23aa
-- title:
--   Permutation orders with the offset logarithmic integral
-- statement:
--   For sufficiently large $n$, the bound for the maximal permutation order uses the inverse of $x\mapsto\int_2^x dt/\log t$. This is the normalization of the linked platform proof. Theorem 10.42 has its own principal-value target. [Source](https://prove2.me/theorems/261c0ac9-aa9d-41d0-9bfe-82ece896587e).
--
--   Prove2Me solution file:
--
--   ```lean
--   import Theorems.Thm_riemann_hypothesis
--   import Theorems.Thm_LandauFunction_landau_of_riemannHypothesis
--
--   theorem solution :
--       ∀ᶠ n : ℕ in Filter.atTop, Real.log (LandauFunction.landau n) < Real.sqrt (LandauFunction.logIntegralInv n) := by
--     exact LandauFunction.landau_of_riemannHypothesis riemann_hypothesis
--   ```
--
--   **Independent reading of the Lean statement (GPT-6 (Codex))**
--
--   There is a natural number $N$ such that for every natural number $n\ge N$, $\log g(n)<\sqrt{b(n)}$. Here $g(n)$ is the largest order of a permutation of an $n$-element set, and the order is the least positive power that gives the identity. For real $y$, $b(y)=\inf\{x\in\mathbb R:x\ge2,\ y\le\int_2^x(\log t)^{-1}\,dt\}$. The real argument of $b$ in the inequality is the integer $n$ viewed as a real number. The cutoff $N$ is unspecified.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I §10.10. https://doi.org/10.1017/9781108178228

import Mathlib
import Definitions.Def_LandauFunction_landau
import Definitions.Def_LandauFunction_logIntegral

namespace BroughanRH

theorem landau :
    ∀ᶠ n : ℕ in Filter.atTop, Real.log (LandauFunction.landau n) < Real.sqrt (LandauFunction.logIntegralInv n) := by sorry

end BroughanRH
