-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenCount_claim_1
-- name    : EvenCycleTuran.EvenCount.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:43.790147+00:00
-- url     : https://prove2.me/theorems/b4b863c6-05c3-4e8c-b074-7bac5598dfb4
-- title:
--   Claim 1, p. 9 — in a C_{2k}-free graph Σ_{b≠a} f(a, b) ≤ (2k−2)n for every vertex a
-- statement:
--   Let $k\ge2$ and let $G$ be a $C_{2k}$-free graph on $n$ vertices. For every vertex $a$,
--   $$\sum_{b\in V(G)\setminus\{a\}}f(a,b)\le(2k-2)n,$$
--   where $f(a,b)$ is the number of common neighbours of $a$ and $b$.
--
--   The left-hand side is the number of paths on three vertices starting at $a$. Claim 1 bounds each one-variable sum of codegrees in the proof of the upper bound of Theorem 10.
--
--   **Formalization Note** The page states Claim 1 for every $k$ of Theorem 10, i.e. $k\ge2$; the hypothesis is written out.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 9, Claim 1

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenCount_Setting

namespace EvenCycleTuran.EvenCount
open Finset SimpleGraph

theorem claim_1 (k : ℕ) (hk : 2 ≤ k) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (cycleGraph (2 * k)).Free G) (a : V) :
    ∑ b ∈ univ.erase a, EvenCycleTuran.C4Count.codeg G a b ≤ (2 * k - 2) * Fintype.card V := by sorry

end EvenCycleTuran.EvenCount
