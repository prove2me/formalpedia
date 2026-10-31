-- Prove2me | Theorems.Thm_Erdos624_colour_loss_mean_bound
-- name    : Erdos624.colour_loss_mean_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-30T14:10:53.338699+00:00
-- url     : https://prove2.me/theorems/0104ac38-e41c-4b67-8b98-1580a36c24f9
-- title:
--   Colour-loss averaging under pointwise domination (L) (Erdős 624)
-- statement:
--   If $\ell(a)\le d(a)$ for all $a$ in a finite type and $\sum d\le (E+c)|\alpha|$, then $\sum\ell\le (E+c)|\alpha|$. This is the averaging step in the colour-loss bound for clipping.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. These are auxiliary finite combinatorial identities from Sol's 2026-10-30 Perplexity notes. They do **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 17: Sol's Perplexity Computer notes from task d32c2107-b546-4015-be2e-c9c4e46ce7cd (captured 2026-10-30 under perplexity_2026-10-30/), derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 30 2026). Auxiliary finite results only; do NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem colour_loss_mean_bound {α : Type*} [Fintype α]
    (ℓ d : α → ℝ) (E c : ℝ)
    (hℓ : ∀ a, ℓ a ≤ d a)
    (hd : ∑ a : α, d a ≤ (E + c) * Fintype.card α) :
    ∑ a : α, ℓ a ≤ (E + c) * Fintype.card α := by sorry

end Erdos624
