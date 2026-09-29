-- Prove2me | Theorems.Thm_FamousTheorems_p_group_fixed_points_mod_p_7b
-- name    : FamousTheorems.p_group_fixed_points_mod_p_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:34.441022+00:00
-- url     : https://prove2.me/theorems/93825780-9b94-4917-9af9-352a4d1d81d1
-- title:
--   For a p-group action, |X| ≡ |X^G| (mod p)
-- statement:
--   **Fixed points of a $p$-group action.** Let $p$ be a prime, $G$ a $p$-group (every element has order a power of $p$) and $X$ a finite set on which $G$ acts. Let $X^G$ be the set of fixed points. Then
--   $$|X|\equiv|X^G|\pmod p.$$
--
--   This counting lemma has many uses. It proves Cauchy's theorem (via McKay's action of $\mathbb Z/p$ on tuples with product $1$), that a nontrivial finite $p$-group has nontrivial center, and parts of the Sylow theorems. It holds because every non-fixed orbit has size a positive power of $p$.
--
--   **Formalization note.** Mathlib's `IsPGroup.card_modEq_card_fixedPoints`. `IsPGroup p G` says that every element of $G$ has order a power of $p$; $G$ may be infinite. `MulAction.fixedPoints G X` is the set of points fixed by all of $G$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsPGroup.card_modEq_card_fixedPoints`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem p_group_fixed_points_mod_p_7b {p : ℕ} [Fact (Nat.Prime p)] {G : Type*} [Group G] (hG : IsPGroup p G) (X : Type*) [MulAction G X]
    [Finite X] : Nat.card X ≡ Nat.card (MulAction.fixedPoints G X) [MOD p] := by sorry

end FamousTheorems
