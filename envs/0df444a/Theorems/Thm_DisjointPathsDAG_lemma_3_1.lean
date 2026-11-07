-- Prove2me | Theorems.Thm_DisjointPathsDAG_lemma_3_1
-- name    : DisjointPathsDAG.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:31:48.482784+00:00
-- url     : https://prove2.me/theorems/f1e32df7-601b-460f-94ed-8b24cabce233
-- title:
--   Lemma 3.1 (Witness monomials)
-- statement:
--   In the setting of Section 3, let $F$ be a finite field, $G$ a directed or undirected graph, $H_1,\dots,H_k$ arc sets and $\mathcal R=(R,I,(a_i,b_i))$ a regional instance with $a_i,b_i\in R$. Write $n_R=|R|$. Then:
--
--   1. distinct solutions have distinct monomials;
--   2. the monomial of every solution is squarefree, has degree at most $\max\{n_R-1,0\}$, and has coefficient $1$ in $F_R$;
--   3. $F_R\ne0$ if and only if a solution exists;
--   4. if a solution exists, then for a uniform $\xi\in F^E$,
--   $$\Pr\bigl[F_R(\xi)\neq0\bigr]\ge 1-\frac{n_R}{|F|}.$$
--
--   This is the detection test of the paper: a single random evaluation of the enumerating polynomial decides, with one-sided error, whether a solution exists.
--
--   Differences from the source:
--   - encoding: $\max\{n_R-1,0\}$ → natural-number subtraction `ρ.R.card - 1`; reason: the same number
--   - encoding: probability for a uniform $\xi\in F^E$ → the fraction of points of `Fin M → F` with nonzero value; reason: the uniform law on a finite set
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 3.1 (Witness monomials), p.7

import Mathlib
import Definitions.Def_DisjointPathsDAG_Regional

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 3.1 (Witness monomials), p.7: "For every
regional instance, distinct solutions have distinct squarefree monomials of degree at most
max{nR − 1, 0}, each with coefficient 1. Hence FR is a nonzero polynomial exactly when a solution
exists, and then FR(ξ) ≠ 0 with probability at least 1 − nR/|F| for a uniform ξ ∈ F^E."

Setting of Section 3: a finite field `F`, a directed or undirected graph `G` on `V` with edges `Fin M`
(`ends`), arc sets `H i` of orientations of edges, and a regional instance `ρ` whose terminals lie in
`R`. Then
1. distinct solutions have distinct monomials;
2. the monomial of every solution is squarefree, has degree at most `n_R − 1` (natural subtraction, i.e.
   `max{n_R − 1, 0}`), and has coefficient `1` in `F_R`;
3. `F_R ≠ 0` iff a solution exists;
4. if a solution exists, the fraction of points `ξ ∈ F^E` with `F_R(ξ) ≠ 0` is at least `1 − n_R/|F|`.

**Formalization Note** The uniform probability over `F^E` is the fraction of points of the finite set
`Fin M → F`. -/
theorem lemma_3_1 {V : Type} [Fintype V] [DecidableEq V] {M k : ℕ} (F : Type) [Field F] [Fintype F]
    [DecidableEq F] (ends : Fin M → V × V) (H : Fin k → Set (Fin M × Bool)) (ρ : RegInst V k)
    (hρ : ρ.WF) :
    (∀ P P' : ρ.I → List (Fin M × Bool), ρ.IsSol ends H P → ρ.IsSol ends H P' → P ≠ P' →
      solExp ρ P ≠ solExp ρ P') ∧
    (∀ P : ρ.I → List (Fin M × Bool), ρ.IsSol ends H P →
      (∀ e, solExp ρ P e ≤ 1) ∧ (solExp ρ P).sum (fun _ d => d) ≤ ρ.R.card - 1 ∧
      (regionalPoly F ends H ρ).coeff (solExp ρ P) = 1) ∧
    (regionalPoly F ends H ρ ≠ 0 ↔ ∃ P, ρ.IsSol ends H P) ∧
    ((∃ P, ρ.IsSol ends H P) →
      1 - (ρ.R.card : ℝ) / Fintype.card F ≤
        ((Finset.univ.filter fun ξ : Fin M → F => eval ξ (regionalPoly F ends H ρ) ≠ 0).card : ℝ) /
          Fintype.card (Fin M → F)) := by sorry

end DisjointPathsDAG
