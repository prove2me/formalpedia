-- Prove2me | Theorems.Thm_FamousTheorems_lym_inequality
-- name    : FamousTheorems.lym_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:46.66799+00:00
-- url     : https://prove2.me/theorems/2cf36cc7-2f08-4e31-8e85-2582509b6d33
-- title:
--   The Lubell–Yamamoto–Meshalkin (LYM) inequality
-- statement:
--   **The LYM inequality.** Let $X$ be a finite set with $|X|=n$ and $\mathcal A$ an antichain of subsets of $X$ (no member contains another). If $a_r$ is the number of members of $\mathcal A$ of size $r$, then
--   $$\sum_{r=0}^{n}\frac{a_r}{\binom nr}\le1 .$$
--
--   Since $\binom nr\le\binom n{\lfloor n/2\rfloor}$, it gives Sperner's theorem immediately: an antichain in $2^X$ has at most $\binom n{\lfloor n/2\rfloor}$ members. The Lubell–Yamamoto–Meshalkin inequality is a model for counting arguments with chains in extremal set theory.
--
--   **Formalization note.** Mathlib's `Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`, specialised to rational coefficients. `𝒜.slice r` is the subfamily of members of size $r$, and `IsAntichain (· ⊆ ·)` is the antichain condition.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem lym_inequality {α : Type*} [Fintype α] {𝒜 : Finset (Finset α)} (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    ∑ r ∈ Finset.range (Fintype.card α + 1), ((𝒜.slice r).card / (Fintype.card α).choose r : ℚ) ≤ 1 := by sorry

end FamousTheorems
