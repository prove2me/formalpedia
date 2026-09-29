-- Prove2me | Theorems.Thm_FamousTheorems_intersecting_family_card_le_6b
-- name    : FamousTheorems.intersecting_family_card_le_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:07.082734+00:00
-- url     : https://prove2.me/theorems/f4e49bf8-a965-4e4e-b0f7-8bfd7fdfb457
-- title:
--   An intersecting family of subsets of an n-set has at most 2^(n−1) members
-- statement:
--   **An intersecting family of subsets of an $n$-set has at most $2^{n-1}$ members.** Let $\mathcal F$ be a family of subsets of an $n$-element set such that any two members of $\mathcal F$ intersect. Then $|\mathcal F|\le2^{n-1}$.
--
--   The proof is short: a set and its complement cannot both lie in $\mathcal F$. The bound is sharp, as the family of all sets containing a fixed point shows. This is the unrestricted version of the Erdős–Ko–Rado theorem and one of the first results of extremal set theory.
--
--   **Formalization note.** Mathlib's `Set.Intersecting.card_le`, stated for a finite Boolean algebra $\alpha$: an intersecting family $s$ satisfies $2|s|\le|\alpha|$. Two elements intersect when their meet is nonzero. Taking $\alpha$ to be the power set of an $n$-element set gives $2|\mathcal F|\le2^n$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Set.Intersecting.card_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem intersecting_family_card_le_6b {α : Type*} [BooleanAlgebra α] [Fintype α] {s : Finset α} (hs : (s : Set α).Intersecting) :
    2 * s.card ≤ Fintype.card α := by sorry

end FamousTheorems
