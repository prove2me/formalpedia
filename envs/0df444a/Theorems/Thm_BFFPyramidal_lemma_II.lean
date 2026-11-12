-- Prove2me | Theorems.Thm_BFFPyramidal_lemma_II
-- name    : BFFPyramidal.lemma_II
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-13T18:26:16.861659+00:00
-- url     : https://prove2.me/theorems/62fad81c-07d7-4fe6-9708-75dcf9a32189
-- title:
--   Cosets against a subgroup of least prime index
-- statement:
--   **Lemma II.** Let $G$ be a finite group with a subgroup $G_1$ whose index is the least prime factor of $|G|$, and let $K \le G$ be any subgroup and $a \in G$. Then exactly one of two things happens: either the coset $aK$ lies entirely inside the single coset $aG_1$, or $aK$ meets *every* coset of $G_1$, that is $aK \cap bG_1 \ne \emptyset$ for all $b \in G$.
--
--   This dichotomy is what allows an induction along a chain of subgroups of least prime index: a coset of the partition either descends to the quotient or spreads over all of it, with nothing in between.
--
--   **Formalization note.** The conclusion is stated as a disjunction of the inclusion $aK \subseteq aG_1$ and the assertion that $aK \cap bG_1$ is nonempty for every $b$. The hypothesis is `G₁.index = Nat.minFac (Nat.card G)`. The two alternatives are not asserted to be mutually exclusive; only that at least one holds. Cosets are pointwise multiples of sets (`open Pointwise`).
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, p. 140, Lemma II and eqs. (6)-(7)

import Mathlib
open Pointwise

namespace BFFPyramidal

theorem lemma_II {G : Type*} [Group G] [Finite G] (G₁ : Subgroup G)
    (hG₁ : G₁.index = Nat.minFac (Nat.card G)) (K : Subgroup G) (a : G) :
    (a • (K : Set G)) ⊆ (a • (G₁ : Set G)) ∨
      ∀ b : G, ((a • (K : Set G)) ∩ (b • (G₁ : Set G))).Nonempty := by
  sorry

end BFFPyramidal
