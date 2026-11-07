-- Prove2me | Theorems.Thm_DisjointPathsDAG_lemma_3_2
-- name    : DisjointPathsDAG.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:31:57.967709+00:00
-- url     : https://prove2.me/theorems/356b2b1d-f520-41e8-933c-86b5972a84d6
-- title:
--   Lemma 3.2 (Cut factorization)
-- statement:
--   In the setting of Section 3 over a finite field $F$, let $(L,U)$ be a monotone cut of a regional instance $\mathcal R$ (terminals in $R$) with active labels $J$, $j=|J|$. Fix values $\xi_e$ of all noncut variables and let $Q(z)$ be $F_R$ with the cut variables left free. Then:
--
--   1. $Q$ is homogeneous of degree $j$;
--   2. $Q$ is multilinear;
--   3. for every set $B$ of $j$ cut edges,
--   $$[z^B]\,Q=\sum_{\sigma}F^\sigma_L(\xi)\,F^\sigma_U(\xi),$$
--   where $\sigma$ ranges over the feasible bijections $J\to B$, of which there are at most $j!$;
--   4. if $[z^B]Q\neq0$, some feasible $\sigma$ has $F^\sigma_L(\xi)\neq0$ and $F^\sigma_U(\xi)\neq0$.
--
--   Here $F^\sigma_L$, $F^\sigma_U$ are the regional polynomials of the low and the high child under $\sigma$. A nonzero coefficient thus splits a solution into compatible pieces on both sides of the cut.
--
--   Differences from the source: none.
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 3.2 (Cut factorization), p.8

import Mathlib
import Definitions.Def_DisjointPathsDAG_Regional

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

open Classical in
/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 3.2 (Cut factorization), p.8: "Let (L, U)
be a monotone cut of a regional instance R. Fix values ξe of all noncut variables, and let Q(z) be FR
with the cut variables ze left free. Then Q is homogeneous multilinear of degree j, and every collection
B of j cut edges satisfies [zB]Q = ∑σ FσL(ξ)FσU(ξ), where σ ranges over the at most j! feasible
bijections J → B. In particular, if [zB]Q ≠ 0, then some feasible σ has FσL(ξ) ≠ 0 and FσU(ξ) ≠ 0."

In the setting of Section 3 over a finite field `F`, let `(L, U)` be a monotone cut of `ρ` (terminals in
`R`), `J` its active labels, `j = |J|`, and `Q` the regional polynomial with every noncut variable `e`
fixed to `ξ e`. Then
1. `Q` is homogeneous of degree `j`;
2. `Q` is multilinear (every monomial of its support is squarefree);
3. for every set `B` of `j` cut edges, the coefficient of `z^B` in `Q` is the sum, over the feasible
   bijections `σ : J ≃ B`, of `F^σ_L(ξ) F^σ_U(ξ)`, and there are at most `j!` feasible bijections;
4. if that coefficient is nonzero, some feasible `σ` has `F^σ_L(ξ) ≠ 0` and `F^σ_U(ξ) ≠ 0`.

**Formalization Note** `F^σ_L`, `F^σ_U` are the regional polynomials of `lowChild` and `highChild`;
`setExp B` is the exponent of `z^B`. -/
theorem lemma_3_2 {V : Type} [Fintype V] [DecidableEq V] {M k : ℕ} (F : Type) [Field F] [Fintype F]
    [DecidableEq F] (ends : Fin M → V × V) (H : Fin k → Set (Fin M × Bool)) (ρ : RegInst V k)
    (hρ : ρ.WF) (L U : Finset V) (hcut : IsMonotoneCut ends H ρ L U) (ξ : Fin M → F) :
    (cutRestrict ends L U ξ (regionalPoly F ends H ρ)).IsHomogeneous (activeSet ρ L).card ∧
    (∀ d ∈ (cutRestrict ends L U ξ (regionalPoly F ends H ρ)).support, ∀ e, d e ≤ 1) ∧
    (∀ B : Finset (Fin M), B ⊆ cutEdges ends L U → B.card = (activeSet ρ L).card →
      (cutRestrict ends L U ξ (regionalPoly F ends H ρ)).coeff (setExp B) =
        ∑ σ ∈ (Finset.univ : Finset (activeSet ρ L ≃ B)).filter (IsFeasibleBij ends H ρ L),
          eval ξ (regionalPoly F ends H (lowChild ends ρ L σ)) *
            eval ξ (regionalPoly F ends H (highChild ends ρ L U σ)) ∧
      ((Finset.univ : Finset (activeSet ρ L ≃ B)).filter (IsFeasibleBij ends H ρ L)).card ≤
        (activeSet ρ L).card.factorial) ∧
    (∀ B : Finset (Fin M), B ⊆ cutEdges ends L U → B.card = (activeSet ρ L).card →
      (cutRestrict ends L U ξ (regionalPoly F ends H ρ)).coeff (setExp B) ≠ 0 →
      ∃ σ : activeSet ρ L ≃ B, IsFeasibleBij ends H ρ L σ ∧
        eval ξ (regionalPoly F ends H (lowChild ends ρ L σ)) ≠ 0 ∧
        eval ξ (regionalPoly F ends H (highChild ends ρ L U σ)) ≠ 0) := by sorry

end DisjointPathsDAG
