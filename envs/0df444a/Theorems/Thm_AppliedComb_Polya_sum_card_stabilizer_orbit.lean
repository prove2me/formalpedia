-- Prove2me | Theorems.Thm_AppliedComb_Polya_sum_card_stabilizer_orbit
-- name    : AppliedComb.Polya.sum_card_stabilizer_orbit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:43:37.649198+00:00
-- url     : https://prove2.me/theorems/749fe71b-daf1-4898-b86d-46eb076c1cb0
-- title:
--   Proposition 15.8 — the stabilizers over an equivalence class add up to |G|
-- statement:
--   Let a finite group $G$ act on a finite set $\mathcal C$, the action of $\pi \in G$ being written $\pi^*$, and let $\sim$ be the induced equivalence relation: $C \sim C'$ when $\pi^*(C) = C'$ for some $\pi \in G$. Write $\langle C\rangle$ for the equivalence class of $C$ and $\operatorname{stab}_G(C') = \{\pi \in G : \pi^*(C') = C'\}$ for the stabilizer of $C'$. Then for every $C \in \mathcal C$,
--
--   $$\sum_{C' \in \langle C\rangle} |\operatorname{stab}_G(C')| = |G|.$$
--
--   This is the counting step on which the book's proof of Burnside's Lemma rests.
--
--   **Formalization Note.** The action is a Mathlib `MulAction G 𝒞`, with `Fintype G` since $|G|$ appears. The class $\langle C\rangle$ is the finset of $C'$ with `∃ π, π • C = C'`, and $\operatorname{stab}_G(C')$ is `MulAction.stabilizer G C'`. The statement follows quickly from Mathlib's orbit–stabilizer theorem `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 298, Proposition 15.8

import Mathlib

namespace AppliedComb.Polya

/-- Keller–Trotter, Proposition 15.8 (p. 298). Let a group `G` act on a finite set `𝒞`. Then
for all `C ∈ 𝒞`, `∑_{C' ∈ ⟨C⟩} |stab_G(C')| = |G|`, where `⟨C⟩` is the equivalence class of `C`
under the equivalence relation induced by the action (the orbit of `C`) and
`stab_G(C') = {π ∈ G : π^*(C') = C'}`. `G` is finite (`|G|` appears). -/
theorem sum_card_stabilizer_orbit {G 𝒞 : Type*} [Group G] [Fintype G] [Fintype 𝒞]
    [DecidableEq 𝒞] [MulAction G 𝒞] (C : 𝒞) :
    ∑ C' ∈ Finset.univ.filter (fun C' : 𝒞 => ∃ π : G, π • C = C'),
        Nat.card (MulAction.stabilizer G C') = Fintype.card G := by sorry

end AppliedComb.Polya
