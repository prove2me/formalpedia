-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_corollary_3_9
-- name    : BLTCounting.AccuracySpace.corollary_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:27.035157+00:00
-- url     : https://prove2.me/theorems/b15f64f5-cd85-4dcb-bf9a-aff500f93ecb
-- title:
--   Lower bound on the Toeplitz symbol
-- statement:
--   Let $h>0$ and $\theta\in[-\pi,\pi]$. The symbol $\widehat a_h(\theta)$ of equation (21) satisfies
--   $$\widehat a_h(\theta)\ge\frac1h\,\widehat c_0\Bigl(\frac\theta h\Bigr).$$
--   This lower-bounds the symbol on the interval where the transform of $c_0$ is large.
--
--   **Formalization Note.** $\widehat a_h$ is a complex series, so the conclusion includes that its imaginary part vanishes, and the inequality is between real parts.
--
--   Differences from the source:
--   - generalization: the inherited width $h$ of Section 3 → every $h>0$, with the inherited $\theta\in[-\pi,\pi]$; reason: the bound holds for every positive $h$; the source statement is the special case
--   - encoding: an inequality of real numbers → imaginary part of $\widehat a_h(\theta)$ stated to vanish, inequality on real parts; reason: Lean convention for complex-valued series; same quantity
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Corollary 3.9, printed p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

namespace BLTCounting.AccuracySpace

/-- Corollary 3.9, PDF p. 20: for `h > 0` and `θ ∈ [-π, π]`, the symbol `â_h(θ)` is real and
`â_h(θ) ≥ (1/h) ĉ₀(θ/h)`. -/
theorem corollary_3_9 (h θ : ℝ) (hh : 0 < h) (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi) :
    (sampledSymbol h θ).im = 0 ∧
      (1 / h) * (c0Hat (θ / h)).re ≤ (sampledSymbol h θ).re := by sorry

end BLTCounting.AccuracySpace
