-- Prove2me | Theorems.Thm_AggCG_lemma_I_1
-- name    : AggCG.lemma_I_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:33.965422+00:00
-- url     : https://prove2.me/theorems/2511daab-8a9c-4e3d-97c1-0a028b4ef9e4
-- title:
--   Lemma I.1 — root behavior of the two gadgets
-- statement:
--   Let $a>\beta\ge 1$ be naturals, $S\subsetneq[m]$ nonempty, $u\in[0,1]^m$, and $\sigma=\sum_{t\in S}u_t$.
--
--   1. The root LP has the unique optimum $(x,y)=(\beta/a,0)$, of value $\beta/a$ on $L(a,\beta;S)$ and $-\beta/a$ on $G(a,\beta;S)$.
--   2. The unique integer optimum is $(0,0)$ on $L$, of value $0$, and $(1,0)$ on $G$, of value $-1$.
--   3. One-node trees are characterized by
--   $$\mathrm{TreeSize}_u(L)=1\iff\sigma\in[1/a,1/\beta),\qquad \mathrm{TreeSize}_u(G)=1\iff\sigma>0\text{ and }\lceil a\sigma\rceil=\lceil\beta\sigma\rceil.$$
--   4. All runs of branch and bound have the same size, and it is $1$ or $3$; it is $1$ exactly when the root LP with the cut has an integral optimum.
--   5. $\mathrm{LP}(I)>\mathrm{IP}(I)$, $0\le g_u(I)\le 1$, and $\mathrm{TreeSize}_u(I)=1\iff g_u(I)=1$.
--
--   This is the computation on which every later statement rests.
--
--   **Formalization Note** Tree size and gap are computed from branch and bound and the LP values, not from the closed forms.
--
--   Differences from the source:
--   - reading: an unspecified "LP-based B&B" solver that counts all generated nodes → the relation BBSize over every LP optimum and every fractional variable, without pruning by bound; TreeSize is its least size; reason: the paper names no solver; on every gadget the optimum is unique and all runs have one size (lemma_I_1)
--   - encoding: a > β ≥ 1 in the integral data of §I.1 → a, β natural numbers; reason: the paper requires integral data
--   - encoding: a unique LP solution, "precisely three generated nodes", g_u defined when LP(I) > IP(I) → explicit clauses: uniqueness of the optimum, the size relation is single-valued with value 1 or 3, and a positive denominator; reason: these are stated in the surrounding text of the lemma on p.49 and are what the definitions need
-- source:
--   Sharma, Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms, STOC 2027 submission (manuscript sha256 f7ea0248…), Lemma I.1, pp.49–50 (PDF pp.50–51); §I.1, p.49 for 0 ≤ g_u ≤ 1

import Definitions.Def_AggCG_gapClosed
import Definitions.Def_AggCG_BBSize
import Definitions.Def_AggCG_Gadget

namespace AggCG

/-- **Lemma I.1** (Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), pp.49–50, PDF pp.50–51): the root behavior of the two gadgets, for all `a > β ≥ 1` and nonempty `S ⊊ [m]`
(no bound `a ≤ 8`, any `|S|`), and every `u ∈ [0,1]^m`. The root LP has the unique optimum `(β/a, 0)`, and the integer optimum is `(0, 0)` on `L`, `(1, 0)` on `G`;
one-node trees are characterized by `σ ∈ [1/a, 1/β)` on `L` and by `σ > 0 ∧ ⌈aσ⌉ = ⌈βσ⌉` on `G`. All runs of B&B have the same size, it is `1` or `3`, and it is `1` exactly when the root with the cut has an integral optimum.
`g_u` is defined with positive denominator, `0 ≤ g_u ≤ 1`, and `g_u = 1` exactly at one-node trees.

**Formalization Note** `TreeSize` and `g_u` are computed from B&B and the LP values, not from the closed forms. The value of the root LP is `c⊤(β/a, 0)`, i.e. `β/a` on `L` and `−β/a` on `G`. -/
theorem lemma_I_1 {m : ℕ} (G : Gadget m) (hG : G.Admissible) (u : Fin m → ℝ) (hu : InUnitBox u) :
    (∀ z, G.toIP.IsLPOpt none [] z ↔ z = ![(G.β : ℝ) / G.a, 0]) ∧
    (G.kind = .L →
      G.toIP.LPval = (G.β : ℝ) / G.a ∧ G.toIP.IPval = 0 ∧
      (∀ z, G.toIP.IsIntOpt z ↔ z = ![0, 0]) ∧
      (treeSize G.toIP u = 1 ↔ 1 / (G.a : ℝ) ≤ G.sigma u ∧ G.sigma u < 1 / (G.β : ℝ))) ∧
    (G.kind = .G →
      G.toIP.LPval = -((G.β : ℝ) / G.a) ∧ G.toIP.IPval = -1 ∧
      (∀ z, G.toIP.IsIntOpt z ↔ z = ![1, 0]) ∧
      (treeSize G.toIP u = 1 ↔ 0 < G.sigma u ∧ ⌈(G.a : ℝ) * G.sigma u⌉ = ⌈(G.β : ℝ) * G.sigma u⌉)) ∧
    (∀ k, BBSize G.toIP (G.toIP.cutOf u) [] k ↔ k = treeSize G.toIP u) ∧
    (treeSize G.toIP u = 1 ∨ treeSize G.toIP u = 3) ∧
    ((∃ z, G.toIP.IsLPOpt (some (G.toIP.cutOf u)) [] z ∧ IsIntegralPt z) ↔ treeSize G.toIP u = 1) ∧
    G.toIP.IPval < G.toIP.LPval ∧
    0 ≤ G.toIP.gapClosed u ∧ G.toIP.gapClosed u ≤ 1 ∧
    (treeSize G.toIP u = 1 ↔ G.toIP.gapClosed u = 1) := by sorry

end AggCG
