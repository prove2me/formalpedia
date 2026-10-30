-- Prove2me | Theorems.Thm_FlexMargin_claim_A
-- name    : FlexMargin.claim_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:40:32.046359+00:00
-- url     : https://prove2.me/theorems/82042bc2-5442-46d4-8a78-c52f4166383d
-- title:
--   Claim A: odd sequences with many and with few high profit products
-- statement:
--   Consider a long chain with $n/2$ high profit and $n/2$ low profit products, $n$ even, and call $k$ consecutive product nodes along the chain (cyclically) a **sequence of length $k$**. For every $1\le k\le n/2-1$:
--
--   1. there is a sequence of length $2k+1$ with at least $k+1$ high profit products, and
--   2. there is a sequence of length $2k+1$ with at most $k$ high profit products.
--
--   Claim A is the first step of the proof of Lemma 3(a).
--
--   Differences from the source:
--   - encoding: a long chain with n/2 high and n/2 low products; a sequence of length k is k consecutive product nodes (cyclically) → the products in chain order τ 0, ..., τ (n−1) for an arbitrary product permutation τ; windowCount counts the products of a category among τ (s + j mod n), j < len; reason: every long chain is L relabelled, and its plant permutation does not affect which products are consecutive; same instances
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), Appendix A, Claim A, p. 46

import Mathlib
import Definitions.Def_FlexMargin_windowCount

open Finset

namespace FlexMargin

/-- **Claim A (proof of Lemma 3(a)).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), Appendix A, Claim A, p. 46: "For any 1 ≤ k ≤ n/2−1, (i) there exists a sequence of length
2k + 1 with at least k + 1 high profit products, and (ii) there exists a sequence of length 2k + 1 with
at most k high profit products."

Context (p. 46): "Consider a long chain with n/2 low profit products and n/2 high profit products,
where n is an even integer. We call a consecutive sequence of k product nodes a sequence of length k."
The long chain is the standard chain relabelled by the product permutation `τ`; its products in chain
order are `τ 0, …, τ (n-1)`, and a sequence of length `len` starting at `s` is `τ s, τ (s+1), …` taken
cyclically (`FlexMargin.windowCount`). Categories: `1` high, `0` low; there are as many of each.

**Formalization Note.** The plant permutation of the long chain plays no role and is omitted;
`τ` ranges over all permutations, so every long chain is covered. -/
theorem claim_A (n : ℕ) (cat : Fin n → Fin 2)
    (hbal : (univ.filter (fun i => cat i = 1)).card = (univ.filter (fun i => cat i = 0)).card)
    (τ : Equiv.Perm (Fin n)) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n / 2 - 1) :
    (∃ s : Fin n, k + 1 ≤ windowCount cat τ s (2 * k + 1) 1) ∧
      (∃ s : Fin n, windowCount cat τ s (2 * k + 1) 1 ≤ k) := by sorry

end FlexMargin
