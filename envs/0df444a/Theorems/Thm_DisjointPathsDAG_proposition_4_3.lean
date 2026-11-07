-- Prove2me | Theorems.Thm_DisjointPathsDAG_proposition_4_3
-- name    : DisjointPathsDAG.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:32.968204+00:00
-- url     : https://prove2.me/theorems/e159e37f-0722-491d-80f3-d83fe8a9b42c
-- title:
--   Proposition 4.3 (Row sweep)
-- statement:
--   For every $k\ge3$ there are a constant $C$ and a generator program such that, for every instance of the setting of Theorem 4.1 (vertices numbered in a topological order), the generator writes, within $C(\text{size}+1)$ machine steps, a division-free program $P$ with integer constants whose output is the polynomial $F$ as an identity of formal polynomials (hence over every commutative ring), with
--
--   $$\operatorname{size}(P)\le C\,(mn^{k-2}+n^k),\qquad \operatorname{space}(P)\le C\,n^{k-1}.$$
--
--   This is the combinatorial bound of the paper, valid over every commutative ring without fast matrix multiplication.
--
--   Differences from the source:
--   - generalization: a program over the given commutative ring $R$ → one program over $\mathbb Z$ with integer constants computing $F$ as a formal polynomial; reason: the formal identity maps to every commutative ring; specializes to the source
--   - encoding: a DAG with a given topological order → the vertex numbering is the order (`IsTopo`: tail < head); reason: every DAG has one
--   - encoding: "constructed in time linear in its length" → `GeneratesSLP`: a machine generator halting within `C * (size + 1)` steps on every tape; reason: the machine of Section 2.1
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Proposition 4.3 (Row sweep), p.13

import Mathlib
import Definitions.Def_DisjointPathsDAG_Encoding

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Proposition 4.3 (Row sweep), p.13: "In the
setting of Theorem 4.1, a division-free straight-line program with Ok(mnk−2 + nk) ring operations
computes F. The program is constructed in time linear in its length and can be executed in Ok(nk−1)
space."

For every `k ≥ 3` there are a constant `C`, a width constant `A` and a machine program `Gen` such that,
for every instance of the setting of Theorem 4.1 (vertices numbered in a topological order), `Gen` on the
instance's words writes, in at most `C · (size + 1)` steps, a division-free program `P` with integer
constants whose output is the polynomial `F` as an identity of formal polynomials over `ℤ` (hence over
every commutative ring), with `size P ≤ C · (m n^(k−2) + n^k)` and `space P ≤ C · n^(k−1)`.

**Formalization Note** A formal identity over `ℤ` with integer constants maps to every commutative ring
`R` (the same program over `R`, constants `natTable R`). Edge `e` is input `e`. The exponents `k − 2`,
`k − 1` are natural numbers with `k ≥ 3`. -/
theorem proposition_4_3 :
    ∀ k : ℕ, 3 ≤ k → ∃ (C : ℝ) (A : ℕ) (Gen : Program), 0 < C ∧ 1 ≤ A ∧
      ∀ (n m : ℕ) (S : Setting n m k), S.G.IsTopo →
        GeneratesSLP Gen A (encodeInst S) C fun P =>
          P.formalOut (natTable ℤ) 0 = rename Fin.val (enumPoly S.G S.H S.pairs) ∧
          (P.size : ℝ) ≤ C * ((m : ℝ) * (n : ℝ) ^ (k - 2) + (n : ℝ) ^ k) ∧
          (P.space : ℝ) ≤ C * (n : ℝ) ^ (k - 1) := by sorry

end DisjointPathsDAG
