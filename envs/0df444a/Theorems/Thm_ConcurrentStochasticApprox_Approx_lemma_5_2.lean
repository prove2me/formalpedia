-- Prove2me | Theorems.Thm_ConcurrentStochasticApprox_Approx_lemma_5_2
-- name    : ConcurrentStochasticApprox.Approx.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:06.662179+00:00
-- url     : https://prove2.me/theorems/9a9814c3-4f30-4a61-b2ce-ed75fc25eb7b
-- title:
--   Lemma 5.2 — sign of rational combinations of power-series numbers in polynomial time
-- statement:
--   Let $x_1,\dots,x_k\in F(\ell,B)$ and let $c_1,\dots,c_k$ be rational numbers defined using at most $B_{\mathrm{inp}}$ bits. Then the sign of
--   $$\sum_{i=1}^k c_ix_i$$
--   is decided in time polynomial in $k$, $\ell$, $B$ and $B_{\mathrm{inp}}$.
--
--   Every check of the verifier (shrinking inequalities, widths, comparisons with a threshold) is such a sign computation, with the rational input data as coefficients.
--
--   Differences from the source:
--   - generalization: time polynomial in k, ℓ, B and B_inp → a Cook machine computing the sign (as the integer −1, 0 or 1) from the binary encoding of the list of pairs (c_i, x_i) in time polynomial in the length of that encoding; reason: the encoding length is at most polynomial in k, ℓ, B, B_inp (k pairs, each with at most ℓ terms of O(B) bits and a coefficient of O(B_inp) bits), so this implies the source bound
-- source:
--   Ali Asadi, Krishnendu Chatterjee, The Computational Complexity of Concurrent Stochastic Games: Exact Value and Approximation, STOC 2027 submission #285 (October 2026), SHA-256 5cff187cf6b230b3bdfe540f2832f824d1ddb6acb43239fbf469d37c43b0d461, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/285.pdf, Lemma 5.2, printed p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_ConcurrentStochasticApprox_Approx_PowerSeries
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
open Finset NetworkEquilibriumCLS.LinearNash

namespace ConcurrentStochasticApprox.Approx

/-- **Lemma 5.2 (Rational coefficients).** The sign of `∑_{i=1}^k c_i x_i`, for power-series numbers
`x_i` and rational coefficients `c_i`, is computed in polynomial time from the binary encoding of
the list of pairs `(c_i, x_i)`. -/
theorem lemma_5_2 :
    ∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ terms : List (ℚ × PSNum),
        f (encList (fun p => encRat p.1 ++ encPS p.2) terms) =
          encInt ((SignType.sign ((terms.map fun p => (p.1 : ℝ) * psVal p.2).sum) : SignType) : ℤ) := by sorry

end ConcurrentStochasticApprox.Approx
