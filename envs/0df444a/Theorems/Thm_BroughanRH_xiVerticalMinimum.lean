-- Prove2me | Theorems.Thm_BroughanRH_xiVerticalMinimum
-- name    : BroughanRH.xiVerticalMinimum
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:20:48.745677+00:00
-- url     : https://prove2.me/theorems/027ed911-5d58-42b3-af6d-db7f14fa4d4e
-- title:
--   The minimum of the logarithmic derivative on a vertical line
-- statement:
--   On the vertical line of real part $\sigma>1/2$, the real part of $\xi^\prime/\xi$ attains its infimum at $t=0$. This specializes the zero-free half-plane in Theorem 10.35 to $a=1/2$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 10.35. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem xiVerticalMinimum :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    ∀ σ t : ℝ, 1/2 < σ →
      (deriv xi (σ : ℂ) / xi (σ : ℂ)).re ≤
      (deriv xi ((σ : ℂ) + (t : ℂ) * Complex.I) / xi ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by sorry

end BroughanRH
