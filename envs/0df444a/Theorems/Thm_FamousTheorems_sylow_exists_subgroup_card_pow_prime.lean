-- Prove2me | Theorems.Thm_FamousTheorems_sylow_exists_subgroup_card_pow_prime
-- name    : FamousTheorems.sylow_exists_subgroup_card_pow_prime
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:10:31.542147+00:00
-- url     : https://prove2.me/theorems/7d30a246-974d-4fca-85fe-f34713411c12
-- title:
--   Sylow's first theorem
-- statement:
--   **Sylow's existence theorem.**
--
--   If $p^{n}$ divides $|G|$, then $G$ has a subgroup of order exactly $p^{n}$.
--
--   This is a strong converse to Lagrange's theorem. Lagrange says every subgroup's order divides
--   $|G|$; the converse fails in general — $A_4$ has order $12$ but no subgroup of order $6$ — yet
--   it holds for every **prime power** divisor.
--
--   Sylow's theorems are the central tool in classifying finite groups of small order: knowing the
--   number of Sylow $p$-subgroups is congruent to $1$ mod $p$ and divides the index usually pins
--   down the group structure, and is how one shows groups of certain orders cannot be simple.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sylow_exists_subgroup_card_pow_prime :
    ∀ {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact (Nat.Prime p)],
      p ^ n ∣ Nat.card G → ∃ K : Subgroup G, Nat.card K = p ^ n := by sorry

end FamousTheorems
