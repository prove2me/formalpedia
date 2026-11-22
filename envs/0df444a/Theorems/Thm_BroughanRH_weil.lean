-- Prove2me | Theorems.Thm_BroughanRH_weil
-- name    : BroughanRH.weil
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-22T14:21:47.105419+00:00
-- url     : https://prove2.me/theorems/f89bf6d0-557d-4573-816b-2a895649aefe
-- title:
--   Weil positivity in additive coordinates
-- statement:
--   In the additive-coordinate test space already formalized on Prove2Me, the real part of the Weil distribution applied to $g*g^*$ is nonnegative for every smooth compactly supported complex test function. [Source](https://prove2.me/theorems/22770c57-ee68-4a0c-96e7-e0ef164a79f9).
--
--   Prove2Me solution file:
--
--   ```lean
--   import Theorems.Thm_riemann_hypothesis
--   import Theorems.Thm_ConnesRZFrontier_weilPositive_iff_mathlib_RH
--
--   theorem solution :
--       ∀ g : ℝ → ℂ, ConnesRZ.IsTest g → 0 ≤ (ConnesRZ.weilDistribution (ConnesRZ.conv g (ConnesRZ.starInv g))).re := by
--     exact ConnesRZFrontier.weilPositive_iff_mathlib_RH.mpr riemann_hypothesis
--   ```
--
--   **Independent reading of the Lean statement (GPT-6 (Codex))**
--
--   For every real-smooth, compactly supported function $g:\mathbb R\to\mathbb C$, form $h(t)=\int_{\mathbb R}g(s)\overline{g(s-t)}\,ds$ and $M(z)=\int_{\mathbb R}h(t)e^{(z-1/2)t}\,dt$ for $z\in\mathbb C$. Then $\operatorname{Re}\!\left(M(0)+M(1)-\sum_{n=0}^{\infty}\frac{\Lambda(n)}{\sqrt n}\bigl(h(\log n)+h(-\log n)\bigr)+\frac1{2\pi}\int_{\mathbb R}M(1/2+ir)\bigl(\operatorname{Re}((\Gamma'/\Gamma)(1/4+ir/2))-\log\pi\bigr)\,dr\right)\ge0$. Here $\Gamma$ is the complex gamma function and $\Lambda(n)$ is $\log p$ for $n$ a positive power of the prime $p$ and zero otherwise. The term at $n=0$ is zero under the conventions $\log0=0$ and division by zero equal to zero. All integrals use Lebesgue measure.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §9.5. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

namespace BroughanRH

theorem weil :
    ∀ g : ℝ → ℂ, ConnesRZ.IsTest g → 0 ≤ (ConnesRZ.weilDistribution (ConnesRZ.conv g (ConnesRZ.starInv g))).re := by sorry

end BroughanRH
