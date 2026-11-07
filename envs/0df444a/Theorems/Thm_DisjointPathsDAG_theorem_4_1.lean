-- Prove2me | Theorems.Thm_DisjointPathsDAG_theorem_4_1
-- name    : DisjointPathsDAG.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:19.145112+00:00
-- url     : https://prove2.me/theorems/d075df1d-bd31-4418-8c93-ff48cd90e62a
-- title:
--   Theorem 4.1 — $F$ by straight-line programs of size $O_k(mn^{k-2}+n^k)$, or $O_k(m+n^{k-3+\alpha})$
-- statement:
--   Fix $k\ge3$. Let $G$ be a DAG with $n$ vertices, $m$ edges and a given topological order, $H_1,\dots,H_k$ spanning edge subgraphs and $(s_1,t_1),\dots,(s_k,t_k)$ vertex pairs ($s_i=t_i$ allowed), and let
--   $$F=\sum_{(P_1,\dots,P_k)}\prod_{i=1}^k\prod_{e\in E(P_i)}x_e$$
--   over the tuples of pairwise vertex-disjoint paths with $P_i$ an $s_i$–$t_i$ path in $H_i$. Then:
--
--   1. a generator writes, in time linear in the length of its output, a division-free program with integer constants of size $O_k(mn^{k-2}+n^k)$ and space $O_k(n^{k-1})$ that computes $F$ as a formal polynomial, hence over every commutative ring;
--   2. for every $\alpha>2$ and every generator $\mathrm{gen}$ of multiplication programs, a generator writes, in time linear in its length, a division-free program of size $O_k(m+n^{k-3+\alpha})$ that evaluates $F$ over every commutative ring $R$ over which $\mathrm{gen}$ multiplies $h\times h$ matrices with $O(h^\alpha)$ operations by programs constructible in linear time.
--
--   This is the main algebraic result of the paper.
--
--   Differences from the source:
--   - generalization: a program over the given commutative ring $R$ → one program over $\mathbb Z$ with integer constants computing $F$ as a formal polynomial; reason: the formal identity maps to every commutative ring; specializes to the source
--   - generalization: a program for the given ring $R$ under its hypothesis → constants and generator depending only on $\alpha$, `gen`, $A'$, $C'$, serving every ring and table; reason: the construction does not inspect the ring; specializes to the source
--   - generalization: the matrix-multiplication hypothesis and "computes F" as identities of formal polynomials (Section 2.2, p.6) → `MMSpec` asks for the product as a function on $R$-matrices, and the conclusion asks for $F$ as a function on $R^E$; reason: the hypothesis is weaker; applied to the ring $R[X]$ with the table `C ∘ cst` (a formal hypothesis over $R$ gives the functional one over $R[X]$), the same generator, chosen before the ring, yields the formal identity over $R$, so the statement specializes to the source
--   - encoding: "h × h matrices over R can be multiplied by a division-free straight-line program that is constructible in time linear in its length and uses O(h^α) operations" → `MMSpec R α cst gen A' C'`; reason: the hypothesis about a machine generator
--   - encoding: a DAG with a given topological order → the vertex numbering is the order (`IsTopo`: tail < head); reason: every DAG has one
--   - encoding: "constructed in time linear in its length" → `GeneratesSLP`: a machine generator halting within `C * (size + 1)` steps on every tape; reason: the machine of Section 2.1
--   - reading: "then Ok(m + n^{k−3+α}) operations suffice" → the second clause keeps the linear construction time; reason: "suffice" refers to the same construction
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 4.1, p.10

import Mathlib
import Definitions.Def_DisjointPathsDAG_Encoding
import Definitions.Def_DisjointPathsDAG_MMHyp

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 4.1, p.10: "Fix an integer k ≥ 3. Let G
be a DAG with n vertices, m edges, and a given topological order, let H1, . . . , Hk be spanning
edge-subgraphs of G, and let (s1, t1), . . . , (sk, tk) be vertex pairs, where si = ti is allowed.
Assign an element xe of a commutative ring R to every edge e of G, and let
F := ∑(P1,...,Pk) ∏ki=1 ∏e∈E(Pi) xe, where the sum ranges over all tuples of pairwise vertex-disjoint
paths such that Pi is an si–ti path in Hi. With unit-cost ring operations, F is computed by a
division-free straight-line program with Ok(mnk−2 + nk) operations, which is constructed in time linear
in its length and executed in Ok(nk−1) space. If h × h matrices over R can be multiplied by a
division-free straight-line program that is constructible in time linear in its length and uses O(hα)
operations for some α > 2, then Ok(m + nk−3+α) operations suffice."

For every `k ≥ 3`:
1. there are `C`, `A` and a generator `Gen` that, on every instance (vertices numbered in a topological
   order), writes in at most `C · (size + 1)` steps a division-free program with integer constants whose
   output is `F` as a formal polynomial over `ℤ` (hence over every commutative ring), of size at most
   `C · (m n^(k−2) + n^k)` and space at most `C · n^(k−1)`;
2. for every `α > 2` and every multiplication generator `gen` (constants `A'`, `C'`) there are `C`, `A`
   and a generator `Gen` such that, for every commutative ring `R` and table `cst` satisfying the
   multiplication hypothesis (`MMSpec`), `Gen` writes in at most `C · (size + 1)` steps a division-free
   program (constants `mixTable cst`) whose output is `F(x)` at every point, of size at most
   `C · (m + n^(k−3+α))`.

**Formalization Note** "Then Ok(m + nk−3+α) operations suffice" refers to the same construction, so the
second clause keeps the linear construction time. The topological order is the numbering of the vertices
(`IsTopo`). -/
theorem theorem_4_1 :
    ∀ k : ℕ, 3 ≤ k →
      (∃ (C : ℝ) (A : ℕ) (Gen : Program), 0 < C ∧ 1 ≤ A ∧
        ∀ (n m : ℕ) (S : Setting n m k), S.G.IsTopo →
          GeneratesSLP Gen A (encodeInst S) C fun P =>
            P.formalOut (natTable ℤ) 0 = rename Fin.val (enumPoly S.G S.H S.pairs) ∧
            (P.size : ℝ) ≤ C * ((m : ℝ) * (n : ℝ) ^ (k - 2) + (n : ℝ) ^ k) ∧
            (P.space : ℝ) ≤ C * (n : ℝ) ^ (k - 1)) ∧
      (∀ α : ℝ, 2 < α → ∀ (gen : Program) (A' : ℕ) (C' : ℝ),
        ∃ (C : ℝ) (A : ℕ) (Gen : Program), 0 < C ∧ 1 ≤ A ∧
          ∀ (R : Type) [CommRing R] (cst : ℕ → R), MMSpec R α cst gen A' C' →
          ∀ (n m : ℕ) (S : Setting n m k), S.G.IsTopo →
            GeneratesSLP Gen A (encodeInst S) C fun P =>
              (∀ x : ℕ → R, P.out (mixTable cst) x 0 =
                MvPolynomial.eval₂ (Int.castRingHom R) (fun e : Fin m => x e.val)
                  (enumPoly S.G S.H S.pairs)) ∧
              (P.size : ℝ) ≤ C * ((m : ℝ) + (n : ℝ) ^ ((k : ℝ) - 3 + α))) := by sorry

end DisjointPathsDAG
