-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_lemma_2_7
-- name    : BLTCounting.AccuracySpace.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:44.803406+00:00
-- url     : https://prove2.me/theorems/e09e85db-a7ad-47c9-be2b-097164a7aa6d
-- title:
--   Toeplitz quadratic form
-- statement:
--   Let $(a[t])_{t\in\mathbb Z}$ be absolutely summable with $a[-t]=\overline{a[t]}$, let $T[i,j]=a[i-j]$ for $0\le i,j<K$, and let $a(\theta)=\sum_{t\in\mathbb Z}a[t]e^{it\theta}$. Then for every $u\in\mathbb C^K$,
--   $$u^*Tu=\frac1{2\pi}\int_{-\pi}^{\pi}a(\theta)\,|\widehat u(\theta)|^2\,d\theta,\qquad \widehat u(\theta)=\sum_{j=0}^{K-1}u[j]e^{ij\theta}.$$
--   A lower bound on the symbol on an interval thus gives a lower bound on the quadratic form.
--
--   Differences from the source: none.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 2.7, printed p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

open Matrix

namespace BLTCounting.AccuracySpace

/-- Lemma 2.7 (Toeplitz quadratic form), PDF p. 12: if `(a[t])_{t ∈ ℤ}` is absolutely summable with
`a[-t] = a[t]*` and `T[i, j] = a[i - j]`, then for every `u ∈ ℂ^K`,
`u* T u = (1/2π) ∫_{-π}^{π} a(θ) |û(θ)|² dθ`. -/
theorem lemma_2_7 (a : ℤ → ℂ) (ha : Summable (fun t => ‖a t‖))
    (hconj : ∀ t, a (-t) = star (a t)) (K : ℕ) (u : Fin K → ℂ) :
    star u ⬝ᵥ (toeplitz K a *ᵥ u) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ θ in (-Real.pi)..Real.pi,
          bilateralSymbol a θ * ((‖trigPoly u θ‖ ^ 2 : ℝ) : ℂ) := by sorry

end BLTCounting.AccuracySpace
