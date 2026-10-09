-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_multiplicative_large_sieve
-- name    : ArtinPrimitiveRoots.multiplicative_large_sieve
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T16:44:19.275955+00:00
-- url     : https://prove2.me/theorems/bca6f0b1-35e1-4320-ac57-776fa37ee430
-- title:
--   Multiplicative large sieve (classical; used for Bombieri–Vinogradov)
-- statement:
--   For natural numbers $R \ge 1$, $K$, $H$ and any complex sequence $a : \mathbb N \to \mathbb C$,
--
--   $$\sum_{d=1}^{R} \frac{d}{\varphi(d)} \sum_{\chi \bmod d \text{ primitive}} \Bigl|\sum_{K < n \le K + H} a_n \chi(n)\Bigr|^2 \;\le\; (2R^2 + 13H) \sum_{K < n \le K + H} |a_n|^2.$$
--
--   The inner sum runs over `primChars d`, the Dirichlet characters modulo $d$ of conductor $d$; for $d = 1$ this is the trivial character. Characters are evaluated at $n$ through the cast $\mathbb N \to \mathbb Z/d\mathbb Z$.
--
--   **Formalization note.** The factor $2R^2 + 13H$ is the constant that comes from the analytic large sieve with spacing $\delta = 1/(2R^2)$ and constant $\delta^{-1} + 13N$, as published in `LargeSieve.analytic_large_sieve`. The textbook form has $R^2 + H$ (or $R^2 + H - 1$); any bound of the shape $O(R^2 + H)$ serves the proof of the Bombieri–Vinogradov theorem.
--
--   Reference: Davenport, *Multiplicative Number Theory*, ch. 27. This is a step of the proof of the Bombieri–Vinogradov theorem, which OpenAI's *Primitive roots for every admissible integer base* (2026) applies at (12.16), p. 77.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 77, step of the proof of the Bombieri–Vinogradov theorem (12.16)

import Mathlib
import Definitions.Def_ArtinBV

namespace ArtinPrimitiveRoots

open Finset

theorem multiplicative_large_sieve (R K H : ℕ) (hR : 1 ≤ R) (a : ℕ → ℂ) :
    ∑ d ∈ Icc 1 R, ((d : ℝ) / d.totient) *
        ∑ χ ∈ primChars d, ‖∑ n ∈ Ioc K (K + H), a n * χ n‖ ^ 2
      ≤ (2 * (R : ℝ) ^ 2 + 13 * H) * ∑ n ∈ Ioc K (K + H), ‖a n‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots
