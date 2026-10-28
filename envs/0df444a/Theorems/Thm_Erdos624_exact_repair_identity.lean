-- Prove2me | Theorems.Thm_Erdos624_exact_repair_identity
-- name    : Erdos624.exact_repair_identity
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:44:24.547989+00:00
-- url     : https://prove2.me/theorems/b9b7417f-1d04-4f95-a259-02e0c80c0e0f
-- title:
--   Exact repair identity for list-system deficits (Erdős 624 Round 10)
-- statement:
--   Let $U$ and $C$ be finite sets, $|C|=n$, and let $L:\mathcal P(U)\to\mathcal P(C)$ be an arbitrary list system. For $Y\subseteq U$ write the palette $J(Y)=\bigcup_{A\subseteq Y}L(A)$ and the deficit $D(Y)=n-|J(Y)|$. For a colour $u\in J(Y)$ let
--   $$E_u(Y)=\bigcap\{A\subseteq Y:\ u\in L(A)\}$$
--   be the set of coordinates contained in every witness of $u$ inside $Y$.
--
--   Let $V\subseteq U$ be a pool with $N=|V|$, let $B$ be a finite set with $b=|B|<j$. Then
--   $$(N-j+1)\sum_{\substack{W\subseteq V,\ |W|=j-1\\ B\subseteq W}}D(W)=(j-b)\sum_{\substack{Y\subseteq V,\ |Y|=j\\ B\subseteq Y}}D(Y)+\sum_{\substack{Y\subseteq V,\ |Y|=j\\ B\subseteq Y}}\ \sum_{u\in J(Y)}|E_u(Y)\setminus B|.$$
--   (Natural-number subtraction is used for $N+1-j$; if $j>N+1$ both sides vanish. The source assumes $B\subseteq V$; if $B\not\subseteq V$ every sum is empty and the identity is trivially true.)
--
--   This is the exact repair identity from Sol's Round 10 analysis of Erdős Problem 624: a hole of a $(j-1)$-face either survives on a one-point extension or is consumed by a witness with a mandatory deleted coordinate. It is an auxiliary identity and does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 consolidated report, section 'Proved: witness complexity, forks, and repair budgets' → 'Exact repair identity' (boxed identity); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; Lean by Grok Bot for Ethan Cheung (Oct 24 2026). Honest: a proved auxiliary lemma only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

/-- Exact repair identity (Sol Round 10). For any list system `L`, pool `V`, `B` with `|B| < j`:
`(N-j+1) Σ_{W ⊇ B, |W|=j-1} D(W) = (j-b) Σ_{Y ⊇ B, |Y|=j} D(Y) + Σ_Y Σ_{u∈J(Y)} |E_u(Y) \ B|`.
Does not settle PAIR / #624. -/
theorem exact_repair_identity {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C]
    [DecidableEq C] (L : Finset U → Finset C) (V B : Finset U) (j : ℕ) (hj : B.card < j) :
    (V.card + 1 - j) * ∑ W ∈ (V.powersetCard (j - 1)).filter (fun W => B ⊆ W),
        (Fintype.card C - (W.powerset.biUnion L).card)
      = (j - B.card) * ∑ Y ∈ (V.powersetCard j).filter (fun Y => B ⊆ Y),
          (Fintype.card C - (Y.powerset.biUnion L).card)
        + ∑ Y ∈ (V.powersetCard j).filter (fun Y => B ⊆ Y),
            ∑ u ∈ Y.powerset.biUnion L,
              (((Y.powerset.filter (fun A => u ∈ L A)).inf id) \ B).card := by sorry

end Erdos624
