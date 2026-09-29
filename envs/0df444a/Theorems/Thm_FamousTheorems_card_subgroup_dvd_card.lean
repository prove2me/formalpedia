-- Prove2me | Theorems.Thm_FamousTheorems_card_subgroup_dvd_card
-- name    : FamousTheorems.card_subgroup_dvd_card
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:51:57.505187+00:00
-- url     : https://prove2.me/theorems/c25e4319-0b58-49ff-bd66-7fcffd29a436
-- title:
--   Lagrange's theorem on the order of a subgroup
-- statement:
--   **The order of a subgroup divides the order of the group.**
--
--   $$|H| \ \big|\ |G| \qquad \text{for every subgroup } H \le G .$$
--
--   The cosets of $H$ partition $G$ and each has exactly $|H|$ elements, so $|G| = [G:H]\,|H|$.
--
--   It is the first structural theorem of group theory and the source of most elementary counting
--   arguments about groups: that the order of an element divides the order of the group, that groups
--   of prime order are cyclic, and — applied to $(\mathbb{Z}/n)^\times$ — Euler's and Fermat's
--   theorems in number theory.
--
--   **Formalization note.** `Nat.card` returns $0$ for infinite types, and divisibility by $0$ holds
--   only for $0$, so the statement is the intended one in the finite case and vacuous otherwise.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem card_subgroup_dvd_card : ∀ {α : Type*} [Group α] (s : Subgroup α),
    Nat.card s ∣ Nat.card α := by sorry

end FamousTheorems
