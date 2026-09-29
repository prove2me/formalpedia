-- Prove2me | Theorems.Thm_FamousTheorems_ahlswede_zhang_identity
-- name    : FamousTheorems.ahlswede_zhang_identity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:43.204886+00:00
-- url     : https://prove2.me/theorems/8d4adf1d-e1b3-496d-a546-1f9e33124425
-- title:
--   The Ahlswede–Zhang identity
-- statement:
--   **The Ahlswede–Zhang identity.** Let $X$ be a nonempty finite set with $|X|=n$ and $\mathcal A$ a nonempty family of nonempty subsets of $X$. For $s\subseteq X$ let $\mathcal A_s=\bigcap\{a\in\mathcal A : a\subseteq s\}$ (taken to be $\emptyset$ if no member of $\mathcal A$ lies in $s$). Then
--   $$\sum_{s\subseteq X}\frac{|\mathcal A_s|}{|s|\binom{n}{|s|}}=1 .$$
--
--   This identity strengthens the LYM inequality to an equality. Dropping the correction terms coming from the intersections gives back LYM, and it gives a new proof of Sperner's theorem.
--
--   **Formalization note.** Mathlib's `AhlswedeZhang.infSum_eq_one`, with `AhlswedeZhang.infSum` unfolded. `𝒜.truncatedInf s` is the intersection of the members of $\mathcal A$ contained in $s$ (and $\emptyset$ if there are none), and the sum is computed in `ℚ`, so the term for $s=\emptyset$ is $0/0=0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AhlswedeZhang.infSum_eq_one`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem ahlswede_zhang_identity {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {𝒜 : Finset (Finset α)} (h𝒜₁ : 𝒜.Nonempty) (h𝒜₀ : ∅ ∉ 𝒜) :
    ∑ s : Finset α, ((𝒜.truncatedInf s).card : ℚ) / (s.card * (Fintype.card α).choose s.card) = 1 := by sorry

end FamousTheorems
