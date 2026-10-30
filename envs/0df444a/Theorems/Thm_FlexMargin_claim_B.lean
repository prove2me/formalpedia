-- Prove2me | Theorems.Thm_FlexMargin_claim_B
-- name    : FlexMargin.claim_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:41:02.146436+00:00
-- url     : https://prove2.me/theorems/77123a72-c5ca-48ca-8d16-9f501f63ab28
-- title:
--   Claim B: even sequences with many and with few high profit products
-- statement:
--   Consider a long chain with $n/2$ high profit and $n/2$ low profit products, $n$ even. For every $1\le k\le n/2$:
--
--   1. there is a sequence of $2k$ consecutive products (cyclically) with at least $k$ high profit products, and
--   2. there is a sequence of $2k$ consecutive products with at most $k$ high profit products.
--
--   Claim B is the first step of the proof of Lemma 3(b).
--
--   Differences from the source:
--   - encoding: a long chain with n/2 high and n/2 low products; a sequence of length k is k consecutive product nodes (cyclically) → the products in chain order τ 0, ..., τ (n−1) for an arbitrary product permutation τ; windowCount counts the products of a category among τ (s + j mod n), j < len; reason: every long chain is L relabelled, and its plant permutation does not affect which products are consecutive; same instances
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), Appendix A, Claim B, p. 47

import Mathlib
import Definitions.Def_FlexMargin_windowCount

open Finset

namespace FlexMargin

/-- **Claim B (proof of Lemma 3(b)).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), Appendix A, Claim B, p. 47: "For any 1 ≤ k ≤ n/2, (i) there exists a sequence of length 2k with
at least k high profit products, and (ii) For any 1 ≤ k ≤ n/2, there exists a sequence of length 2k with
at most k high profit products."

Context (p. 46): "Consider a long chain with n/2 low profit products and n/2 high profit products,
where n is an even integer. We call a consecutive sequence of k product nodes a sequence of length k."
The long chain is the standard chain relabelled by the product permutation `τ`; its products in chain
order are `τ 0, …, τ (n-1)`, and a sequence of length `len` starting at `s` is `τ s, τ (s+1), …` taken
cyclically (`FlexMargin.windowCount`). Categories: `1` high, `0` low; there are as many of each.

**Formalization Note.** The plant permutation is omitted (it plays no role); `τ` ranges over all
permutations. -/
theorem claim_B (n : ℕ) (cat : Fin n → Fin 2)
    (hbal : (univ.filter (fun i => cat i = 1)).card = (univ.filter (fun i => cat i = 0)).card)
    (τ : Equiv.Perm (Fin n)) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n / 2) :
    (∃ s : Fin n, k ≤ windowCount cat τ s (2 * k) 1) ∧
      (∃ s : Fin n, windowCount cat τ s (2 * k) 1 ≤ k) := by sorry

end FlexMargin
