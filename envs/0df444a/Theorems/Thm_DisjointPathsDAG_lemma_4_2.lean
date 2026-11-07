-- Prove2me | Theorems.Thm_DisjointPathsDAG_lemma_4_2
-- name    : DisjointPathsDAG.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:21.983387+00:00
-- url     : https://prove2.me/theorems/0c8466f1-4c81-49ac-bbe6-89f7c19971b9
-- title:
--   Lemma 4.2 (First-event decomposition)
-- statement:
--   In the setting of Theorem 4.1 ($k\ge3$, a DAG with its vertices numbered in a topological order, edge subgraphs $H_i$, pairs $(s_i,t_i)$), over every commutative ring and for every assignment $x$ of ring elements to the edges:
--
--   1. for every endpoint tuple $e$ and real vertex $w$, the tuples $A\in\Omega(e)$ whose earliest collision is $w$ have total weight $B^w(e)$;
--   2. for $|S|\ge2$, a real vertex $v$ and $c_i<v$ for $i\notin S$, with $e_i=v$ for $i\in S$ and $e_i=c_i$ otherwise,
--   $$\Lambda_S(v;c)=\prod_{i=1}^kL_i(e_i)-\sum_{w\in V:\,w<v}B^w(e);\tag{1}$$
--   3. with $\theta=(\theta_1,\dots,\theta_k)$,
--   $$F=\prod_{i=1}^kL_i(\theta_i)-\sum_{w\in V}B^w(\theta).\tag{2}$$
--
--   These recurrences let every table row be computed from rows with earlier meeting vertices, which is what the row sweep and the batched algorithms evaluate.
--
--   Differences from the source:
--   - generalization: endpoint tuples and the tuples $c$, $d$ of vertices of $H^+_i$ → tuples of arbitrary extended vertices; reason: the private terminals of other commodities are isolated in $H^+_i$ and contribute $0$; specializes to the source
--   - encoding: the extended graphs $H^+_i$ and the order → extended vertices `Fin (k + n + k)` ordered by value, arcs `Fin m ⊕ Bool`; reason: same graphs and order
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 4.2 (First-event decomposition), p.12

import Mathlib
import Definitions.Def_DisjointPathsDAG_FirstEvent

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

open Classical in
/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 4.2 (First-event decomposition), p.12:
"For every endpoint tuple e and real vertex w, the tuples A ∈ Ω(e) whose earliest collision is w have
total weight Bw(e). Consequently, for S, v, c as in the definition of ΛS, and for ei := v when i ∈ S and
ei := ci otherwise, ΛS(v; c) = ∏ki=1 Li(ei) − ∑w∈V: w<v Bw(e). (1) Moreover, with θ := (θ1, . . . , θk),
F = ∏ki=1 Li(θi) − ∑w∈V Bw(θ). (2) These identities hold over every commutative ring."

In the setting of Theorem 4.1 (`k ≥ 3`, `G` with its vertices numbered in a topological order, edge
subgraphs `Hᵢ`, pairs `(sᵢ, tᵢ)`), over every commutative ring `R` and for every `x : E → R`:
1. for every endpoint tuple `e` and real vertex `w`, the total weight of the tuples of `Ω(e)` whose
   earliest collision is `w` is `Bʷ(e)`;
2. identity (1), for `|S| ≥ 2`, a real vertex `v`, and `cᵢ < v` for `i ∉ S`;
3. identity (2), where `F` is the value of the polynomial of Theorem 4.1 at `x`.

**Formalization Note** Endpoint tuples range over all extended vertices; the private terminals of the
other commodities are isolated vertices of `H⁺ᵢ`, and no tuple of `Ω(e)` reaches them, so this adds
only instances with both sides `0`. -/
theorem lemma_4_2 {n m k : ℕ} (hk : 3 ≤ k) (S : Setting n m k) (hS : S.G.IsTopo) (R : Type)
    [CommRing R] (x : Fin m → R) :
    (∀ (e : Fin k → XV k n) (w : Fin n),
      ∑ A ∈ (Omega S e).filter (fun A => IsEarliestCollision S A w), tupleWt x A = Bw S x w e) ∧
    (∀ (T : Finset (Fin k)) (v : Fin n) (c : Fin k → XV k n), 2 ≤ T.card →
      (∀ i, i ∉ T → c i < real v) →
      Lam S x T v c = ∏ i, Lsum S x i (endpt T v c i) -
        ∑ w ∈ Finset.univ.filter (· < v), Bw S x w (endpt T v c)) ∧
    MvPolynomial.eval₂ (Int.castRingHom R) x (enumPoly S.G S.H S.pairs) =
      ∏ i, Lsum S x i (snk i) - ∑ w : Fin n, Bw S x w (fun i => snk i) := by sorry

end DisjointPathsDAG
