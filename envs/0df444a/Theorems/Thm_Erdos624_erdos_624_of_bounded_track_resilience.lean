-- Prove2me | Theorems.Thm_Erdos624_erdos_624_of_bounded_track_resilience
-- name    : Erdos624.erdos_624_of_bounded_track_resilience
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:30:07.760398+00:00
-- url     : https://prove2.me/theorems/e2f44f1d-be03-4375-b878-6421b2804da7
-- title:
--   Bounded-track resilience implies Erdős Problem 624
-- statement:
--   Let $H(n)$ be as in Erdős Problem 624.
--
--   **Theorem.** Suppose that for every fixed $r$ there is $K$ such that for every $k\ge K$ and every $r$ maps $g_1,\dots,g_r:\mathcal P(U)\to U$ with $|U|=2^k$, some $k$-set $Y\subseteq U$ and some $u\in U$ satisfy $g_i(A)\ne u$ for all $i$ and all $A\subseteq Y$ (bounded-track resilience). Then
--
--   $$H(n)-\log_2 n\to\infty,$$
--
--   i.e. the Formal Conjectures statement `erdos_624` holds.
--
--   Proof: for $r=2^s$ the hypothesis is $\mathrm{TrackBad}(2^k,k,s)$, so track amplification gives $H(2^k+s)>k+s$ for $k\ge K(s)$. For large $n$ take $k=\lfloor\log_2(n-s)\rfloor\ge\max(K(s),s)$; by monotonicity $H(n)>k+s$, while $n<2^{k+2}$, so $H(n)-\log_2 n>s-2$. Only the cases $r=2^s$ are used.
--
--   This pins down a sufficient statement for #624; whether bounded-track resilience is true is open (already $r=2$ is beyond counting).
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; Claim (B.8) of claim from a GPT answer relayed by Ethan Cheung (third round, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem erdos_624_of_bounded_track_resilience (hB8 : ∀ r : ℕ, ∃ K : ℕ, ∀ k ≥ K, ∀ g : Fin r → Finset (Fin (2 ^ k)) → Fin (2 ^ k),
      ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧ ∃ u : Fin (2 ^ k), ∀ i, ∀ A ⊆ Y, g i A ≠ u) :
    Filter.Tendsto (fun n : ℕ => (H n : ℝ) - Real.logb 2 (n : ℝ)) Filter.atTop Filter.atTop := by sorry

end Erdos624
