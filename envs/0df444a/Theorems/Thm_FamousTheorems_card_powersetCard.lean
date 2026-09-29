-- Prove2me | Theorems.Thm_FamousTheorems_card_powersetCard
-- name    : FamousTheorems.card_powersetCard
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:23.912895+00:00
-- url     : https://prove2.me/theorems/e4fef722-3e60-4efc-a4dc-7ac3739fb131
-- title:
--   The number of $k$-element subsets
-- statement:
--   **The number of $k$-subsets of an $n$-set is $\binom{n}{k}$.**
--
--   $$\#\{T \subseteq S : |T| = k\} \;=\; \binom{|S|}{k}.$$
--
--   This is the combinatorial definition of the binomial coefficient, and the identity that makes
--   $\binom{n}{k} = \frac{n!}{k!(n-k)!}$ a counting statement rather than a formula: order the $k$
--   chosen elements in $n(n-1)\cdots(n-k+1)$ ways, then divide by the $k!$ orderings of each subset.
--
--   Everything from Pascal's rule to the binomial theorem to the hypergeometric distribution rests
--   on reading $\binom{n}{k}$ this way.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem card_powersetCard : ∀ {α : Type*} (n : ℕ) (s : Finset α),
    (Finset.powersetCard n s).card = s.card.choose n := by sorry

end FamousTheorems
