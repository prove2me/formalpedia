-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenCount_eq_2
-- name    : EvenCycleTuran.EvenCount.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:19.204877+00:00
-- url     : https://prove2.me/theorems/ac46e1c4-3df5-4546-b16d-76347636b7ea
-- title:
--   (2), p. 10 — in a C_{2k}-free graph Σ_{a≠b} f(a, b) ≤ (k−1)n² over unordered pairs
-- statement:
--   Let $k\ge2$ and let $G$ be a $C_{2k}$-free graph on $n$ vertices. Then, with the sum over unordered pairs $\{a,b\}$ of distinct vertices,
--   $$\sum_{\{a,b\},\,a\neq b}f(a,b)\le(k-1)n^2.$$
--
--   This follows from Claim 1 by summing over $a$ (each unordered pair is counted twice). It is the linear part of $\sum f^2=2\sum\binom f2+\sum f$ at the end of the proof of Theorem 10.
--
--   **Formalization Note** The sum is over unordered pairs (`Sym2` off the diagonal); over ordered pairs the bound would be $2(k-1)n^2$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 10, eq. (2)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenCount_Setting

namespace EvenCycleTuran.EvenCount
open Finset SimpleGraph

theorem eq_2 (k : ℕ) (hk : 2 ≤ k) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (cycleGraph (2 * k)).Free G) :
    ∑ p ∈ offDiagPairs V, codegPair G p ≤ (k - 1) * Fintype.card V ^ 2 := by sorry

end EvenCycleTuran.EvenCount
