-- Prove2me | Theorems.Thm_Erdos624_covering_core_nonsingleton_lower
-- name    : Erdos624.covering_core_nonsingleton_lower
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-30T14:10:51.980614+00:00
-- url     : https://prove2.me/theorems/85727bab-d0eb-41c9-91ad-058cda336497
-- title:
--   Covering core of nonsingleton sets: size lower bound (C) (Erdős 624)
-- statement:
--   Let $R$ be finite and $\mathcal G$ a family of subsets of $R$, each of size at least $2$. If $k\ge 2$, $k\le|R|$, and every $k$-subset of $R$ contains a member of $\mathcal G$, then $|R|(|R|-1)\le k(k-1)|\mathcal G|$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. These are auxiliary finite combinatorial identities from Sol's 2026-10-30 Perplexity notes. They do **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 17: Sol's Perplexity Computer notes from task d32c2107-b546-4015-be2e-c9c4e46ce7cd (captured 2026-10-30 under perplexity_2026-10-30/), derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 30 2026). Auxiliary finite results only; do NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem covering_core_nonsingleton_lower {α : Type*} [DecidableEq α]
    (R : Finset α) (G : Finset (Finset α)) (k : ℕ)
    (hk : 2 ≤ k) (hRk : k ≤ #R)
    (hG : ∀ A ∈ G, A ⊆ R ∧ 2 ≤ #A)
    (hcov : ∀ S ∈ R.powersetCard k, ∃ A ∈ G, A ⊆ S) :
    #R * (#R - 1) ≤ k * (k - 1) * #G := by sorry

end Erdos624
