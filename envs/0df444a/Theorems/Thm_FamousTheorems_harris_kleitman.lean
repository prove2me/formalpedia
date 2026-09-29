-- Prove2me | Theorems.Thm_FamousTheorems_harris_kleitman
-- name    : FamousTheorems.harris_kleitman
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:39.839988+00:00
-- url     : https://prove2.me/theorems/5221378b-6209-43e2-bc2f-ee16e2dac6fb
-- title:
--   The Harris–Kleitman inequality
-- statement:
--   **The Harris–Kleitman inequality.** Let $X$ be a finite set with $|X|=n$ and let $\mathcal A,\mathcal B$ be down-closed families of subsets of $X$ (lower sets under inclusion). Then
--   $$|\mathcal A|\cdot|\mathcal B|\le 2^n\,|\mathcal A\cap\mathcal B| .$$
--
--   Dividing by $4^n$, this says that decreasing events are positively correlated under the uniform measure on $2^X$. It is the simplest correlation inequality and is generalised by the FKG and Ahlswede–Daykin inequalities. Harris used it in percolation theory, and Kleitman in extremal set theory.
--
--   **Formalization note.** Mathlib's `IsLowerSet.le_card_inter_finset`. Families are `Finset (Finset α)` for a finite type `α` playing the role of $X$. Mathlib also has the variants for two upper sets and for an upper and a lower set.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsLowerSet.le_card_inter_finset`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem harris_kleitman {α : Type*} [DecidableEq α] [Fintype α] {𝒜 ℬ : Finset (Finset α)} (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) : 𝒜.card * ℬ.card ≤ 2 ^ Fintype.card α * (𝒜 ∩ ℬ).card := by sorry

end FamousTheorems
