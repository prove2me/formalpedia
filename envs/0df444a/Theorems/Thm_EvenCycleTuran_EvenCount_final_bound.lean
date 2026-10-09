-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenCount_final_bound
-- name    : EvenCycleTuran.EvenCount.final_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:43.456187+00:00
-- url     : https://prove2.me/theorems/44eb30fc-b321-47ac-bf6c-d83894b645a0
-- title:
--   Theorem 10 proof, p. 10 — 𝒩(C_{2l}, G) ≤ (1/2l) Σ_{u≠v} f²(u,v)·(2k−2)^{l−2} n^{l−2} for C_{2k}-free G
-- statement:
--   Let $l\ge3$, $k\ge2$, and let $G$ be a $C_{2k}$-free graph on $n$ vertices. Then, with the sum over unordered pairs $\{u,v\}$ of distinct vertices,
--   $$\mathcal N(C_{2l},G)\le\frac1{2l}\sum_{\{u,v\},\,u\neq v}f^2(u,v)\,(2k-2)^{l-2}n^{l-2}.$$
--
--   Together with $\sum f^2=2\sum\binom f2+\sum f$, inequality (1) and inequality (2), this gives the upper bound $(1+o(1))\frac{2^{l-2}(k-1)^l}{2l}n^l$ of Theorem 10.
--
--   **Formalization Note** The inequality is stated in $\mathbb R$; the sum is over `Sym2` off the diagonal.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 10, display after "adding up all four cases" (proof of Theorem 10)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenCount_Setting

namespace EvenCycleTuran.EvenCount
open Finset SimpleGraph

theorem final_bound (l k : ℕ) (hl : 3 ≤ l) (hk : 2 ≤ k) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (cycleGraph (2 * k)).Free G) :
    (G.copyCount (cycleGraph (2 * l)) : ℝ) ≤
      1 / (2 * (l : ℝ)) * (∑ p ∈ offDiagPairs V, (codegPair G p : ℝ) ^ 2) *
        (2 * (k : ℝ) - 2) ^ (l - 2) * (Fintype.card V : ℝ) ^ (l - 2) := by sorry

end EvenCycleTuran.EvenCount
