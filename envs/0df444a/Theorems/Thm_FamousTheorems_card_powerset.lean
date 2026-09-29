-- Prove2me | Theorems.Thm_FamousTheorems_card_powerset
-- name    : FamousTheorems.card_powerset
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:20.336507+00:00
-- url     : https://prove2.me/theorems/acde0f72-4096-4c8e-8b48-c44bf90cb529
-- title:
--   The number of subsets of a finite set
-- statement:
--   **A set with $n$ elements has $2^n$ subsets.**
--
--   $$|\mathcal{P}(S)| = 2^{|S|}.$$
--
--   Each element is independently in or out of a subset, giving $2$ choices per element. Equivalently
--   subsets correspond to characteristic functions $S \to \{0,1\}$.
--
--   Summing the binomial coefficients recovers it as $\sum_k \binom{n}{k} = 2^n$, the case $x=y=1$
--   of the binomial theorem. It is the reason exhaustive search over subsets is exponential, and the
--   finite shadow of Cantor's theorem.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem card_powerset : ∀ {α : Type*} (s : Finset α), s.powerset.card = 2 ^ s.card := by sorry

end FamousTheorems
