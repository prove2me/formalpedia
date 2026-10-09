-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenCount_lower_bound_blowup
-- name    : EvenCycleTuran.EvenCount.lower_bound_blowup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:45.751924+00:00
-- url     : https://prove2.me/theorems/1eecdbc5-d58b-41e7-876c-78ac74de897f
-- title:
--   Theorem 10 proof, p. 9 — the blow-up of C_{2l} is C_{2k}-free for 3 ≤ k < l, and its C_{2l}'s are the product of the class sizes
-- statement:
--   Let $3\le k<l$ and $n\ge 2l$, and let $B_{n,l}$ be the blow-up of $C_{2l}$ on $n$ vertices: kept vertices $x_0,\dots,x_{l-1}$, and $l$ classes $S_0,\dots,S_{l-1}$ that split the remaining $n-l$ vertices as evenly as possible, every vertex of $S_i$ being joined to $x_i$ and $x_{i+1}$ (indices mod $l$). Then:
--
--   1. $B_{n,l}$ contains no cycle of length $2k$;
--   2. the number of copies of $C_{2l}$ in $B_{n,l}$ is
--   $$\mathcal N(C_{2l},B_{n,l})=\prod_{i=0}^{l-1}|S_i|.$$
--
--   Since every $|S_i|$ is $\lfloor (n-l)/l\rfloor$ or $\lceil (n-l)/l\rceil$, the product is $(1+o(1))\frac{1}{l^l}n^l$, which is the third bound of Theorem 10. The paper observes that the blow-up contains cycles of length 4 and $2l$ only.
--
--   **Formalization Note** The vertex set is $\{0,\dots,n-1\}$, the kept vertices are $0,\dots,l-1$, and vertex $v\ge l$ lies in class $(v-l)\bmod l$. The paper states the count as $(1+o(1))\frac1{l^l}n^l$; the exact product is stated here, which is what its construction gives.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 9, proof of Theorem 10, second paragraph

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenCount_Setting

namespace EvenCycleTuran.EvenCount
open Finset SimpleGraph

theorem lower_bound_blowup (l k n : ℕ) (hk : 3 ≤ k) (hkl : k < l) (hn : 2 * l ≤ n) :
    EvenCycleTuran.C4Count.CycleFree {2 * k} (blowUp n l) ∧
      (blowUp n l).copyCount (cycleGraph (2 * l)) = ∏ i ∈ range l, #(blowClassSet n l i) := by sorry

end EvenCycleTuran.EvenCount
