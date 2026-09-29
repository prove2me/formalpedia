-- Prove2me | Theorems.Thm_FamousTheorems_glaisher
-- name    : FamousTheorems.glaisher
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:06.565253+00:00
-- url     : https://prove2.me/theorems/22a51cc3-bad3-4da7-ac2c-85f20e351359
-- title:
--   Glaisher's theorem on partitions
-- statement:
--   **Glaisher's theorem.** For every $m\ge1$ and $n$, the number of partitions of $n$ with no part divisible by $m$ equals the number of partitions of $n$ in which no part appears $m$ or more times.
--
--   For $m=2$ this is Euler's theorem (odd parts ↔ distinct parts). Glaisher's bijection (split a part $m^a r$ into $m^a$ copies of $r$) generalises Euler's, and the generating-function proof is the identity $\prod_n \frac{1-x^{mn}}{1-x^n}$ read in two ways.
--
--   **Formalization note.** Mathlib's `Nat.Partition.card_restricted_eq_card_countRestricted`: `restricted n P` is the finset of partitions of `n` whose parts satisfy `P`, and `countRestricted n m` those with every multiplicity `< m`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.Partition.card_restricted_eq_card_countRestricted`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem glaisher (n : ℕ) {m : ℕ} (hm : 0 < m) :
    (Nat.Partition.restricted n fun x => ¬ m ∣ x).card = (Nat.Partition.countRestricted n m).card := by sorry

end FamousTheorems
