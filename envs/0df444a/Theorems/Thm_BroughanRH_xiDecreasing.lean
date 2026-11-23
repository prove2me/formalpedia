-- Prove2me | Theorems.Thm_BroughanRH_xiDecreasing
-- name    : BroughanRH.xiDecreasing
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:22:01.155828+00:00
-- url     : https://prove2.me/theorems/dd8da84f-8906-42de-b4ea-fca89cd68b89
-- title:
--   Horizontal decrease of the xi modulus
-- statement:
--   The modulus of xi decreases strictly along each horizontal line to the left of $\Re s=1/2$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 4.10 (left half-plane). https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem xiDecreasing :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    ∀ t : ℝ, StrictAntiOn (fun σ : ℝ => ‖xi (↑σ + ↑t * Complex.I)‖) (Set.Iio (1/2 : ℝ)) := by sorry

end BroughanRH
