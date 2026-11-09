-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_claim_3_8
-- name    : BLTCounting.AccuracySpace.claim_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:27.380285+00:00
-- url     : https://prove2.me/theorems/7b46e361-9e1d-4fab-b32e-83c77f710da2
-- title:
--   Poisson representation of the Toeplitz symbol
-- statement:
--   Let $h>0$ and $\theta\in[-\pi,\pi]$, and let $\widehat a_h(\theta)=\sum_{t\in\mathbb Z}c_0(ht)e^{-it\theta}$. Then
--   $$\widehat a_h(\theta)=\frac1h\sum_{p\in\mathbb Z}\widehat c_0\Bigl(\frac{\theta+2\pi p}{h}\Bigr).$$
--   Since every term on the right is non-negative, this makes the symbol of the Toeplitz matrix non-negative and comparable to one transform value.
--
--   Differences from the source:
--   - generalization: the width $h$ of the respective section → every $h>0$; reason: the identity holds for every positive $h$; the source statement is the special case
--   - encoding: the identity (23) of two series → convergence of the sampled series and `HasSum` for the Poisson series, instead of an equation of `tsum`s; reason: guards against the Lean default value of a divergent `tsum`; the source asserts the convergence in equation (22)
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Claim 3.8, printed p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

open Complex

namespace BLTCounting.AccuracySpace

/-- Claim 3.8, equation (23), PDF p. 19: for `h > 0` and `θ ∈ [-π, π]`, the sampled-kernel series
`â_h(θ) = ∑_{t ∈ ℤ} c₀(ht) e^{-itθ}` converges, and `â_h(θ) = (1/h) ∑_{p ∈ ℤ} ĉ₀((θ + 2πp)/h)`,
with the right-hand series convergent too. -/
theorem claim_3_8 (h θ : ℝ) (hh : 0 < h) (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi) :
    Summable (fun t : ℤ => ((c0 (h * t) : ℝ) : ℂ) * cexp (-(I * t * θ))) ∧
      HasSum (fun p : ℤ => ((1 / h : ℝ) : ℂ) * c0Hat ((θ + 2 * Real.pi * p) / h))
        (sampledSymbol h θ) := by sorry

end BLTCounting.AccuracySpace
