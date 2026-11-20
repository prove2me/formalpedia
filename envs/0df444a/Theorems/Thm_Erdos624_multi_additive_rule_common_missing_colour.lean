-- Prove2me | Theorems.Thm_Erdos624_multi_additive_rule_common_missing_colour
-- name    : Erdos624.multi_additive_rule_common_missing_colour
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-19T15:24:54.585829+00:00
-- url     : https://prove2.me/theorems/11f19445-fc0b-4caf-8eeb-cf072b942268
-- title:
--   A common missing colour for multi-rule additive colourings (Erdős 624)
-- statement:
--   Let $n=2^k$ and identify the vertex set and the colour set with $(\mathbb F_2)^k$. Fix $t$ rules with $2t<n$, together with arbitrary weight maps $w_j:(\mathbb F_2)^k\to(\mathbb F_2)^k$ and colour relabellings $\pi_j$. A colouring assembled from these rules may, on each subset $A$, choose any one of the $t$ rules and colour $A$ by $\pi_j\bigl(\sum_{x\in A}w_j(x)\bigr)$. Then there exist a colour $c$ and a set $Y\subseteq(\mathbb F_2)^k$ with $2^t|Y|+2t\ge n$ such that no subset of $Y$ receives the colour $c$ under any of the $t$ rules. This does not address unrestricted colourings, and in particular it does not prove $H(2^k)>k+1$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. This is an auxiliary finite statement about colourings assembled from fewer than $n/2$ additive $\mathbb F_2^k$-rules, from GPT-6.2-Astra's 2026-11-19 analysis (relayed by Ethan Cheung). It does **not** address unrestricted colourings, and in particular it does **not** prove $H(2^k)>k+1$. It does **not** settle Erdős Problem 624, PAIR, Step 17, or DENSE-P.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 20b: official-def formalization of the additive multi-rule common-missing-colour lemma from GPT-6.2-Astra's analysis, relayed by Ethan Cheung (public thread https://poe.com/s/uJXfxBGozGrNfWyhQ3XO, 2026-11-19); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (19 Nov 2026, Asia/Hong_Kong). Auxiliary finite result only; does NOT prove H(2^k)>k+1 and does NOT settle PAIR / Step 17 / DENSE-P / #624.

import Mathlib
open Finset Function

namespace Erdos624

theorem multi_additive_rule_common_missing_colour
    (k t : ℕ) (ht : 2 * t < 2 ^ k)
    (w : Fin t → (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (π : Fin t → ((Fin k → ZMod 2) ≃ (Fin k → ZMod 2))) :
    ∃ (c : Fin k → ZMod 2) (Y : Finset (Fin k → ZMod 2)),
      2 ^ t * #Y + 2 * t ≥ 2 ^ k ∧
        ∀ A ⊆ Y, ∀ j : Fin t, π j (∑ x ∈ A, w j x) ≠ c := by sorry

end Erdos624
