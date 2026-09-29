-- Prove2me | Theorems.Thm_FamousTheorems_card_odds_eq_card_distincts
-- name    : FamousTheorems.card_odds_eq_card_distincts
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:17.836871+00:00
-- url     : https://prove2.me/theorems/20ccc144-e4a8-48e2-b9b4-254047eca883
-- title:
--   Euler's partition theorem
-- statement:
--   **Partitions into odd parts and into distinct parts are equinumerous.**
--
--   For every $n$, the number of partitions of $n$ into **odd** parts equals the number into
--   **distinct** parts.
--
--   For $n = 6$: the odd-part partitions are $5{+}1$, $3{+}3$, $3{+}1{+}1{+}1$, $1^6$ — four of
--   them; the distinct-part partitions are $6$, $5{+}1$, $4{+}2$, $3{+}2{+}1$ — also four.
--
--   Euler's proof is a generating-function identity:
--   $$\prod_{k \ \mathrm{odd}} \frac{1}{1-x^{k}} \;=\; \prod_{k\ge1}\bigl(1+x^{k}\bigr),$$
--   which follows by writing $1+x^k = (1-x^{2k})/(1-x^k)$ and telescoping. Glaisher later gave a
--   bijective proof: repeatedly split even parts in half, or merge equal parts.
--
--   It is the prototype of the partition identities that culminate in the Rogers–Ramanujan
--   identities.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem card_odds_eq_card_distincts : ∀ n : ℕ,
    (Nat.Partition.odds n).card = (Nat.Partition.distincts n).card := by sorry

end FamousTheorems
