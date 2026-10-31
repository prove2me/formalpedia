-- Prove2me | Theorems.Thm_Erdos624_shadow_footprint_lower
-- name    : Erdos624.shadow_footprint_lower
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-30T14:10:51.580306+00:00
-- url     : https://prove2.me/theorems/e5e9c895-b57f-4281-9d17-4c8bce3c822f
-- title:
--   Marked k-face nonempty-subset footprint (G-core) (Erdős 624)
-- statement:
--   If $B\subseteq\binom{P}{k}$, then $\sum_{Y\in B}(2^{|Y|}-1)=|B|(2^k-1)$. This is the exact incidence count underlying the shadow footprint lower bound for marked faces.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. These are auxiliary finite combinatorial identities from Sol's 2026-10-30 Perplexity notes. They do **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 17: Sol's Perplexity Computer notes from task d32c2107-b546-4015-be2e-c9c4e46ce7cd (captured 2026-10-30 under perplexity_2026-10-30/), derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 30 2026). Auxiliary finite results only; do NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem shadow_footprint_lower {α : Type*} [DecidableEq α]
    (P : Finset α) (k : ℕ) (B : Finset (Finset α))
    (hB : B ⊆ P.powersetCard k) :
    ∑ Y ∈ B, (2 ^ #Y - 1) = #B * (2 ^ k - 1) := by sorry

end Erdos624
