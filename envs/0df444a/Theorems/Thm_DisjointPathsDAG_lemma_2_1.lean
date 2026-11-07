-- Prove2me | Theorems.Thm_DisjointPathsDAG_lemma_2_1
-- name    : DisjointPathsDAG.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:30:17.239202+00:00
-- url     : https://prove2.me/theorems/87da2802-4426-4c60-b721-f0f004dcb58d
-- title:
--   Lemma 2.1 (Baur–Strassen) — all first partial derivatives in $O(S)$ operations and space
-- statement:
--   There is a constant $C$ such that the following holds over every commutative ring $R$. Let $P$ be a division-free straight-line program of size $S$ whose inputs are variables $x_0,\dots,x_{N-1}$, and let $p$ be the polynomial it computes. Then a division-free program $P'$ with
--
--   $$\operatorname{size}(P')\le C\,S,\qquad \operatorname{space}(P')\le C\,(S+1)$$
--
--   has $N$ outputs, the $i$-th being the formal partial derivative $\partial p/\partial x_i$.
--
--   Evaluating $P'$ at a point $z$ gives all $N$ first partial derivatives of $p$ at $z$. The extraction step of Lemma 3.3 uses this to compute a gradient at the cost of one evaluation.
--
--   **Formalization Note** $P'$ may use the integer constants besides the constants of $P$.
--
--   Differences from the source:
--   - generalization: the $N$ partial derivatives at a given point $z$ → one program computing the $N$ formal partial derivatives; reason: evaluating it at $z$ gives the derivatives at $z$; specializes to the source
--   - encoding: $O(S)$ space → `space P' ≤ C * (P.size + 1)`; reason: the same for $S\ge1$; a program without gates still needs one output register
--   - encoding: constants of $R$ → constant tables `cst` and `mixTable cst`; reason: constants are named by index; same programs
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 2.1 ([BS83]), p.6

import Mathlib
import Definitions.Def_DisjointPathsDAG_SLP

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 2.1 ([BS83], Baur–Strassen), p.6: "Given
a division-free circuit of size S for a polynomial in N variables and a point z, all N first partial
derivatives at z can be computed with O(S) operations and O(S) space."

There is a constant `C` such that, over every commutative ring `R`, for every program `P` of size `S`
whose input gates read variables `0, …, N − 1`, a program `P'` of size at most `C · S` and space at most
`C · (S + 1)` has `N` outputs, output `i` being the formal partial derivative `∂p/∂xᵢ` of the
polynomial `p` computed by `P` (its output `0`).

**Formalization Note** `P'` computes the partial derivatives as formal polynomials, so evaluating it at
any point `z` gives the derivatives at `z`. `P'` may use the integer constants besides those of `P`
(table `mixTable cst`). The space bound is written `C · (S + 1)` because a program with no gate still
needs one register for its outputs; for `S ≥ 1` this is `O(S)`. -/
theorem lemma_2_1 :
    ∃ C : ℕ, ∀ (R : Type) [CommRing R] (cst : ℕ → R) (N : ℕ) (P : SLP),
      (∀ g ∈ P.code, ∀ d i : ℕ, g = Gate.input d i → i < N) →
      ∃ P' : SLP, P'.outs.length = N ∧
        (∀ i < N, P'.formalOut (mixTable cst) i = pderiv i (P.formalOut cst 0)) ∧
        P'.size ≤ C * P.size ∧ P'.space ≤ C * (P.size + 1) := by sorry

end DisjointPathsDAG
