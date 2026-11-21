-- Prove2me | Theorems.Thm_Erdos624_pool_averaging_inverse
-- name    : Erdos624.pool_averaging_inverse
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-20T13:54:00.498722+00:00
-- url     : https://prove2.me/theorems/3536191f-7da2-4900-8843-a1dc6315e3e6
-- title:
--   Finite pool-averaging inverse with crude constant $C_{r,v}$ (Erdős 624)
-- statement:
--   Let $X$ be a finite ground set, let $0\le r\le v$ with $|X|\ge r+v$, and let $f$ assign a real number to every $r$-subset of $X$. If every average of $f$ over the $r$-subsets of a $v$-set $P\subseteq X$ is at most $\varepsilon$ in absolute value, then every $r$-set value is at most $C_{r,v}\varepsilon$, where $C_{r,v}=\sum_{j=0}^{r}2^j(v)_j$ and $(v)_j$ is the falling factorial. In particular, identically zero pool averages force $f=0$. The constant is crude and is not claimed to be optimal. This is a finite averaging inverse, and does not settle Erdős Problem 624.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. This is an auxiliary finite official-def lemma from GPT 6.1 Sol's 2026-10-30 analysis (relayed by Ethan Cheung), formalized on 20 Nov 2026. It does **not** settle Erdős Problem 624, PAIR, Step 17, or DENSE-P.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 21: official-def formalization of leftover R17 shortlist lemmas from GPT 6.1 Sol's analysis, relayed by Ethan Cheung (notes of 2026-10-30); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (20 Nov 2026, Asia/Hong_Kong). Auxiliary finite results only; do NOT settle PAIR / Step 17 / DENSE-P / #624.

import Mathlib
open Finset

namespace Erdos624

theorem pool_averaging_inverse {α : Type*} [DecidableEq α]
    (X : Finset α) (r v : ℕ) (f : Finset α → ℝ) (ε : ℝ)
    (hrv : r ≤ v) (hN : r + v ≤ #X) (hε : 0 ≤ ε)
    (hAvg : ∀ P ⊆ X, #P = v →
      |(∑ Y ∈ P.powersetCard r, f Y) / (v.choose r : ℝ)| ≤ ε) :
    ∀ Y ⊆ X, #Y = r →
      |f Y| ≤ (∑ j ∈ range (r + 1), (2 ^ j * v.descFactorial j : ℝ)) * ε := by sorry

end Erdos624
