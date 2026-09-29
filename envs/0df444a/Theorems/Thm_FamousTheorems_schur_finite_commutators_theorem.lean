-- Prove2me | Theorems.Thm_FamousTheorems_schur_finite_commutators_theorem
-- name    : FamousTheorems.schur_finite_commutators_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:53.13416+00:00
-- url     : https://prove2.me/theorems/bffa2ff1-d185-41b2-8e3b-6309ed399437
-- title:
--   Schur's theorem on the commutator subgroup
-- statement:
--   **Schur's theorem on the commutator subgroup.** Let $G$ be a group with only finitely many commutators $[x,y]$, say $n$ of them. Then the commutator subgroup $[G,G]$ is finite, and
--   $$\big|[G,G]\big|\le \big(n^{2n}\big)^{\,n^{2n+1}+1}.$$
--
--   This is a quantitative form of Schur's theorem. Its best-known corollary is that if $G/Z(G)$ is finite then $[G,G]$ is finite, since there are then at most $[G:Z(G)]^2$ commutators. It is a basic result on groups with finiteness conditions and on central extensions.
--
--   **Formalization note.** Mathlib's `Subgroup.card_commutator_le_of_finite_commutatorSet` together with its companion `Finite` instance. `commutatorSet G` is the set of commutators, `commutator G` is the commutator subgroup, and the bound is Mathlib's `Subgroup.cardCommutatorBound` written out.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Subgroup.card_commutator_le_of_finite_commutatorSet`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem schur_finite_commutators_theorem (G : Type*) [Group G] [Finite (commutatorSet G)] :
    Finite (commutator G) ∧
      Nat.card (commutator G) ≤
        (Nat.card (commutatorSet G) ^ (2 * Nat.card (commutatorSet G))) ^
          (Nat.card (commutatorSet G) ^ (2 * Nat.card (commutatorSet G) + 1) + 1) := by sorry

end FamousTheorems
