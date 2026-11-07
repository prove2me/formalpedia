-- Prove2me | Theorems.Thm_DisjointPathsDAG_proposition_4_5
-- name    : DisjointPathsDAG.proposition_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:30.553371+00:00
-- url     : https://prove2.me/theorems/56c7f31c-bd60-4025-a6d3-0856d1a6b16b
-- title:
--   Proposition 4.5 (Fixed-$k$ batching)
-- statement:
--   Let $k\ge4$, $\alpha>2$ and let $\mathrm{gen}$ be a generator of multiplication programs. There are constants $C$, $D$ and a generator program such that, for every commutative ring $R$ satisfying the matrix-multiplication hypothesis of Proposition 4.4 for $\mathrm{gen}$, and every instance of the setting of Theorem 4.1 with $k$ pairs, the generator writes, within $C(\text{size}+1)$ steps, a division-free program $P$ that evaluates $F$ at every point, with
--
--   $$\operatorname{size}(P)\le C\,(m+n^{k-3+\alpha}),\qquad \operatorname{space}(P)\le D\,n^{k-1}+W,$$
--
--   where $W$ is the largest workspace of a multiplication program for a size $h\le D(n+1)$.
--
--   With $\alpha=\omega+\varepsilon$ this gives the exponent $k-3+\omega+\varepsilon$ of Theorem 4.7 for $k\ge4$.
--
--   Differences from the source:
--   - generalization: a program for the given ring $R$ under its hypothesis → constants and generator depending only on $\alpha$, `gen`, $A'$, $C'$, serving every ring and table; reason: the construction does not inspect the ring; specializes to the source
--   - generalization: the matrix-multiplication hypothesis and "computes F" as identities of formal polynomials (Section 2.2, p.6) → `MMSpec` asks for the product as a function on $R$-matrices, and the conclusion asks for $F$ as a function on $R^E$; reason: the hypothesis is weaker; applied to the ring $R[X]$ with the table `C ∘ cst` (a formal hypothesis over $R$ gives the functional one over $R[X]$), the same generator, chosen before the ring, yields the formal identity over $R$, so the statement specializes to the source
--   - encoding: "h × h matrices over R can be multiplied by a division-free straight-line program that is constructible in time linear in its length and uses O(h^α) operations" → `MMSpec R α cst gen A' C'`; reason: the hypothesis about a machine generator
--   - encoding: a DAG with a given topological order → the vertex numbering is the order (`IsTopo`: tail < head); reason: every DAG has one
--   - encoding: "constructed in time linear in its length" → `GeneratesSLP`: a machine generator halting within `C * (size + 1)` steps on every tape; reason: the machine of Section 2.1
--   - encoding: "stores Ok(n^{k−1}) ring elements in addition to the workspace of the multiplication program" → `space P ≤ D n^(k-1) + mmWork gen A' (D (n + 1))`; reason: the register count of the program
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Proposition 4.5 (Fixed-k batching), p.18

import Mathlib
import Definitions.Def_DisjointPathsDAG_Encoding
import Definitions.Def_DisjointPathsDAG_MMHyp

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Proposition 4.5 (Fixed-k batching), p.18: "Fix
k ≥ 4. Under the matrix multiplication hypothesis of Proposition 4.4, a division-free straight-line
program with Ok(m + nk−3+α) ring operations computes F. It is constructed in time linear in its length
and stores Ok(nk−1) ring elements in addition to the workspace of the multiplication program."

For every `k ≥ 4`, every `α > 2` and every multiplication generator `gen` (constants `A'`, `C'`) there
are constants `C`, `D`, `A` and a machine program `Gen` such that, for every commutative ring `R` and
table `cst` satisfying the hypothesis of Proposition 4.4 (`MMSpec`), and every instance of the setting
of Theorem 4.1 with `k` pairs: `Gen` writes, in at most `C · (size + 1)` steps, a division-free program
`P` (constants `mixTable cst`) whose output is `F(x)` at every point `x`, with
`size P ≤ C · (m + n^(k−3+α))` and `space P ≤ D n^(k−1) + W`, `W` the largest space of a multiplication
program written by `gen` for a size `h ≤ D (n + 1)`.

**Formalization Note** As in Proposition 4.4: functional hypothesis and conclusion, one program for
every ring; `n^(k−3+α)` is `Real.rpow` with the exponent `(k : ℝ) − 3 + α`. -/
theorem proposition_4_5 :
    ∀ k : ℕ, 4 ≤ k → ∀ α : ℝ, 2 < α → ∀ (gen : Program) (A' : ℕ) (C' : ℝ),
      ∃ (C : ℝ) (D A : ℕ) (Gen : Program), 0 < C ∧ 1 ≤ A ∧
        ∀ (R : Type) [CommRing R] (cst : ℕ → R), MMSpec R α cst gen A' C' →
        ∀ (n m : ℕ) (S : Setting n m k), S.G.IsTopo →
          GeneratesSLP Gen A (encodeInst S) C fun P =>
            (∀ x : ℕ → R, P.out (mixTable cst) x 0 =
              MvPolynomial.eval₂ (Int.castRingHom R) (fun e : Fin m => x e.val) (enumPoly S.G S.H S.pairs)) ∧
            (P.size : ℝ) ≤ C * ((m : ℝ) + (n : ℝ) ^ ((k : ℝ) - 3 + α)) ∧
            (P.space : ℕ∞) ≤ ((D * n ^ (k - 1) : ℕ) : ℕ∞) + mmWork gen A' (D * (n + 1)) := by sorry

end DisjointPathsDAG
