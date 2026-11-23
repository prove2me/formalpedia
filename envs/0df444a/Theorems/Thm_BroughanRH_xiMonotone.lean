-- Prove2me | Theorems.Thm_BroughanRH_xiMonotone
-- name    : BroughanRH.xiMonotone
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:21:42.712396+00:00
-- url     : https://prove2.me/theorems/5dc21725-608a-48d5-8ab1-a5e0db74aeff
-- title:
--   Horizontal monotonicity of the xi modulus
-- statement:
--   On every horizontal half-line to the right of the critical line, the modulus of the entire Riemann xi function increases strictly.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 4.10 (right half-plane). https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem xiMonotone :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    ∀ t : ℝ, StrictMonoOn (fun σ : ℝ => ‖xi (↑σ + ↑t * Complex.I)‖) (Set.Ioi (1/2 : ℝ)) := by sorry

end BroughanRH
