-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenCount_c4_codegree_identity
-- name    : EvenCycleTuran.EvenCount.c4_codegree_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:36.094043+00:00
-- url     : https://prove2.me/theorems/d25f57e3-299f-46fe-af9d-704e96fad0fc
-- title:
--   Theorem 10 proof, p. 9 — the number of C₄'s equals ½ Σ_{a≠b} C(f(a,b), 2)
-- statement:
--   Let $G$ be a finite simple graph and, for distinct vertices $a,b$, let $f(a,b)$ be the number of their common neighbours. Then, with the sum over unordered pairs $\{a,b\}$ of distinct vertices,
--   $$2\,\mathcal N(C_4,G)=\sum_{\{a,b\},\,a\neq b}\binom{f(a,b)}{2}.$$
--
--   Each 4-cycle has two pairs of opposite vertices, and a pair $\{a,b\}$ is opposite in exactly $\binom{f(a,b)}{2}$ four-cycles. This identity is how the paper turns Theorem 11, a bound on $\mathcal N(C_4,G)$, into the codegree inequality (1).
--
--   **Formalization Note** The sum is over `Sym2` off the diagonal (unordered pairs). Over ordered pairs the factor would be 4.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 9, proof of Theorem 10, sentence after (1): "the left-hand-side is equal to the number of C4's in G"

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenCount_Setting

namespace EvenCycleTuran.EvenCount
open Finset SimpleGraph

theorem c4_codegree_identity {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    2 * G.copyCount (cycleGraph 4) = ∑ p ∈ offDiagPairs V, (codegPair G p).choose 2 := by sorry

end EvenCycleTuran.EvenCount
