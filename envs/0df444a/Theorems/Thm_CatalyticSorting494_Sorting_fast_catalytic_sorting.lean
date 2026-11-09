-- Prove2me | Theorems.Thm_CatalyticSorting494_Sorting_fast_catalytic_sorting
-- name    : CatalyticSorting494.Sorting.fast_catalytic_sorting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:56.079353+00:00
-- url     : https://prove2.me/theorems/e22f5e41-fc58-4b09-9522-266e767e36e3
-- title:
--   Corollary 1.3 / 3.3 — catalytic sorting of n b-bit numbers in b n^{1+o(1)} time and O(log(n+b)) clean space
-- statement:
--   There is one catalytic machine $M$, one capacity function $c(n,b)$, constants $A,k$, and one function $\varepsilon(n)\to0$ of $n$ alone, with the following property. For all positive integers $n,b$,
--   $$c(n,b)\;\le\;A\,b\,n^{1+\varepsilon(n)}\,\big(\log_2(nb+1)\big)^{k},$$
--   and for every list of $n$ numbers below $2^{b}$, repetitions allowed, and every initial catalytic content $z\in\{0,1\}^{c(n,b)}$, the machine started on the encoded list halts within
--   $$A\,b\,n^{1+\varepsilon(n)}\ \text{ steps, using at most }\ A\,\lfloor\log_2(n+b)\rfloor\ \text{ clean bits,}$$
--   with the sorted list, $nb$ bits long, XORed into the first $nb$ catalytic bits and every other catalytic bit restored.
--
--   Nothing bounds $b$ in terms of $n$, so the time is linear in the key width over the whole range of widths. The catalytic content is adversarial and the machine is deterministic. Without catalytic space, sorting is known to require time-space product $\Omega(n^2)$ in the one-way and constant-pass output models, so this bound is one that clean memory alone cannot match there.
--
--   Differences from the source:
--   - encoding: "O(log(n + b)) clean space and n^{1+o(1)}b time" → explicit A, ε with A·b·n^{1+ε(n)} and A·⌊log₂(n+b)⌋ for all n, b ≥ 1; reason: this is the meaning of the O and o(1) with one algorithm and an exponent depending on n only, as a fixed n forces a time linear in b; ⌊log₂(n+b)⌋ ≥ 1 since n + b ≥ 2.
--   - encoding: "a length-n list of b-bit numbers" and "the sorted list" → the fixed binary formats `encodeKeys` and `sortedOutput`; reason: the source names no format; the output is the sorted list with multiplicities in exactly nb bits.
--   - reading: "catalytic algorithm" with unspecified dirty space → a capacity c(n,b) at most the time bound times (log₂(nb+1))^k; reason: §2, printed p.7, says all the paper's algorithms have catalytic space at most the runtime up to polylogarithmic factors, and the abstract's poly(n) catalytic space is the case b = poly(n).
--   - reading: "RAM access" → a Turing machine with three binary index tapes, charging addresses as clean bits; reason: Definition 2.2 names a Turing machine with random-access heads, and this is the standard reading with the fewest free operations.
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), Corollary 3.3, printed p.12 (PDF p.13), proof ending printed p.13 (PDF p.14); also Corollary 1.3, printed p.3 (PDF p.4)

import Mathlib
import Definitions.Def_CatalyticSorting494_Sorting_Machine
import Definitions.Def_CatalyticSorting494_Sorting_SortingInstance

open Filter Topology

namespace CatalyticSorting494.Sorting

/-- Corollary 1.3 / Corollary 3.3. One machine `M`, one capacity function `c`, one pair of constants
`A, k` and one exponent function `ε → 0` work for all `n, b ≥ 1`, all key lists and all initial
catalytic contents; `ε` depends on `n` only. -/
theorem fast_catalytic_sorting :
    ∃ (M : Machine) (c : ℕ → ℕ → ℕ) (A k : ℕ) (ε : ℕ → ℝ),
      Tendsto ε atTop (𝓝 0) ∧
      ∀ n b : ℕ, 0 < n → 0 < b →
        ((c n b : ℝ) ≤ A * b * (n : ℝ) ^ (1 + ε n) * (Nat.log 2 (n * b + 1) : ℝ) ^ k) ∧
        ∀ keys : List ℕ, IsKeyList n b keys →
          ∀ z : List Bool, z.length = c n b →
            ComputesWithin M (encodeKeys n b keys) z (sortedOutput b keys)
              (A * b * (n : ℝ) ^ (1 + ε n))
              (A * Nat.log 2 (n + b)) := by sorry

end CatalyticSorting494.Sorting
