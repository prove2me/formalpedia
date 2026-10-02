-- Prove2me | Theorems.Thm_AppliedComb_Polya_burnside
-- name    : AppliedComb.Polya.burnside
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:44:02.277389+00:00
-- url     : https://prove2.me/theorems/e63881ef-8241-4d59-a086-b47585939cb8
-- title:
--   Lemma 15.9 — Burnside's Lemma
-- statement:
--   Let a finite group $G$ act on a finite set $\mathcal C$, the action of $\pi \in G$ being written $\pi^*$. For $\pi \in G$ let $\operatorname{fix}_{\mathcal C}(\pi) = \{C \in \mathcal C : \pi^*(C) = C\}$ be the set of elements fixed by $\pi$. If $N$ is the number of equivalence classes of $\mathcal C$ under the equivalence relation induced by the action ($C \sim C'$ when $\pi^*(C) = C'$ for some $\pi \in G$), then
--
--   $$N = \frac{1}{|G|} \sum_{\pi \in G} |\operatorname{fix}_{\mathcal C}(\pi)|.$$
--
--   Burnside's Lemma counts orbits by averaging fixed points; Pólya's Enumeration Theorem refines it by recording the colors used.
--
--   **Formalization Note.** The action is a Mathlib `MulAction G 𝒞` with `Fintype G`; $N$ is `Nat.card (MulAction.orbitRel.Quotient G 𝒞)`, the number of orbits, and $\operatorname{fix}_{\mathcal C}(\pi)$ is `MulAction.fixedBy 𝒞 π`. The identity is stated in $\mathbb Q$, where $|G| \ge 1$. It is Mathlib's `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` after dividing by $|G|$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 298, Lemma 15.9

import Mathlib

namespace AppliedComb.Polya

/-- Keller–Trotter, Lemma 15.9 (Burnside's Lemma), p. 298. Let a group `G` act on a finite set
`𝒞`. If `N` is the number of equivalence classes of `𝒞` induced by this action, then
`N = (1/|G|) ∑_{π ∈ G} |fix_𝒞(π)|`, where `fix_𝒞(π) = {C ∈ 𝒞 : π^*(C) = C}`. The induced
equivalence classes are the orbits (`MulAction.orbitRel`); `G` is finite (`|G|` appears). -/
theorem burnside {G 𝒞 : Type*} [Group G] [Fintype G] [Fintype 𝒞] [MulAction G 𝒞] :
    (Nat.card (MulAction.orbitRel.Quotient G 𝒞) : ℚ) =
      (1 / (Fintype.card G : ℚ)) * ∑ π : G, (Nat.card (MulAction.fixedBy 𝒞 π) : ℚ) := by sorry

end AppliedComb.Polya
