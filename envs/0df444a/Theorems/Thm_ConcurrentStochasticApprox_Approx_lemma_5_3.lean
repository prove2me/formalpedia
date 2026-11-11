-- Prove2me | Theorems.Thm_ConcurrentStochasticApprox_Approx_lemma_5_3
-- name    : ConcurrentStochasticApprox.Approx.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:55.669261+00:00
-- url     : https://prove2.me/theorems/f4356428-a55b-4fbf-89cf-430a0b156e75
-- title:
--   Lemma 5.3 — binary truncation with relative error $2^{1-\ell}$
-- statement:
--   Let $2^B\ge\ell\ge1$ and $x\in(2^{\ell-2^B},1]$. Let $\mathrm{Trunc}_\ell(x)$ be obtained from the binary expansion of $x$ by keeping its first $\ell$ digits, starting from the first nonzero digit, using the finite binary expansion of $x$ when it exists. Then
--   $$\mathrm{Trunc}_\ell(x)\in F_+(\ell,B),\qquad\mathrm{Trunc}_\ell(x)\le x,\qquad\mathrm{rel}(x,\mathrm{Trunc}_\ell(x))\le2^{1-\ell},$$
--   and in particular $(1-2^{1-\ell})x\le\mathrm{Trunc}_\ell(x)\le x$.
--
--   Truncation turns arbitrary probabilities that are not too small into power-series numbers with a controlled relative error.
--
--   Differences from the source:
--   - reading: binary expansion "starting from the first non-zero digit, where we use the finite binary expansion of x if it exists" (the proof writes x = Σ_{i≥1} 2^{-i} x_i) → digits ⌊2^i x⌋ mod 2 for i ≥ 0, so the finite expansion of x = 1 is used and Trunc_ℓ(1) = 1; reason: the statement asks for the finite expansion; for x = 1 the proof convention would give 1 − 2^{-ℓ}; all four conclusions hold under both readings and the domain is unchanged
--   - encoding: rel(x, x') ∈ [0, ∞] with rel(x, 0) = rel(0, x) = ∞ for x > 0 → rel valued in ℝ≥0∞ (ENNReal); reason: the infinite case is represented exactly; no instance changes
-- source:
--   Ali Asadi, Krishnendu Chatterjee, The Computational Complexity of Concurrent Stochastic Games: Exact Value and Approximation, STOC 2027 submission #285 (October 2026), SHA-256 5cff187cf6b230b3bdfe540f2832f824d1ddb6acb43239fbf469d37c43b0d461, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/285.pdf, Lemma 5.3, printed p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_ConcurrentStochasticApprox_Approx_PowerSeries
open Finset

namespace ConcurrentStochasticApprox.Approx

/-- **Lemma 5.3 (Truncation).** Let `2^B ≥ ℓ ≥ 1` and `x ∈ (2^{ℓ - 2^B}, 1]`. Then
`Trunc_ℓ(x) ∈ F₊(ℓ, B)`, `Trunc_ℓ(x) ≤ x`, `rel(x, Trunc_ℓ(x)) ≤ 2^{1-ℓ}`, and
`(1 - 2^{1-ℓ}) x ≤ Trunc_ℓ(x)`. -/
theorem lemma_5_3 (ℓ B : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓB : ℓ ≤ 2 ^ B) (x : ℝ)
    (hx0 : (2 : ℝ) ^ ((ℓ : ℤ) - 2 ^ B) < x) (hx1 : x ≤ 1) :
    trunc ℓ x ∈ Fplus ℓ B ∧ trunc ℓ x ≤ x ∧
      rel x (trunc ℓ x) ≤ ENNReal.ofReal ((2 : ℝ) ^ (1 - (ℓ : ℤ))) ∧
      (1 - (2 : ℝ) ^ (1 - (ℓ : ℤ))) * x ≤ trunc ℓ x := by sorry

end ConcurrentStochasticApprox.Approx
