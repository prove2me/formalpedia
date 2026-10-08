-- Prove2me | Theorems.Thm_Disjunctive_Dominants_facet_support_bound_v2
-- name    : Disjunctive.Dominants.facet_support_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:28.676999+00:00
-- url     : https://prove2.me/theorems/3be2c40b-e7ee-40ed-af8d-b1976d62962e
-- title:
--   Corollary 13.8 — facets of the dominant of a polytope have at most $\dim(P)+1$ nonzero coefficients
-- statement:
--   This is Corollary 13.8 of Balas's *Disjunctive Programming*, an immediate consequence of Theorem 13.7.
--
--   Let $P\subseteq[0,1]^n$ be a polytope and $P^+$ its dominant. If the inequality $\pi x\ge\beta$ defines a facet of $P^+$, that is, if $\{x\in P^+ : \pi x = \beta\}$ is a facet of $P^+$, then
--   $$
--   \big|\{j\in N : \pi_j\neq0\}\big| \le \dim(P)+1 .
--   $$
--
--   **Formalization Note.** The retired version took $P$ to be an arbitrary subset of $\mathbb R^n$. Points with negative coordinates are replaced by their positive parts in the dominant, which can raise the dimension of faces above $\dim P$. A four-point set in a 2-dimensional subspace of $\mathbb R^4$ gave a facet with 4 nonzero coefficients. The new statement requires, as in Theorem 13.7, that $P$ be a polytope (hypothesis `hPoly`) contained in $[0,1]^n$ (`hcube`). Facets are faces of codimension one in the affine-dimension sense (`IsFacet`, `PolyDim`), and $P=\emptyset$ needs no special treatment because then $P^+$ has no facets.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §13.2, p. 221, Corollary 13.8

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

namespace Disjunctive.Dominants

/-- Corollary 13.8 (Balas, *Disjunctive Programming*, Springer 2018, §13.2, p. 221): for a
polytope `P ⊆ [0,1]ⁿ` (the setting of Theorem 13.7), every inequality `πx ≥ β` defining a facet
of the dominant `P⁺` has at most `dim(P) + 1` nonzero coefficients.

Correction w.r.t. the retired version: `P` was an arbitrary subset of `ℝⁿ`; it is now a
polytope (hypothesis `hPoly`) contained in the unit cube (`hcube`). With points having negative
coordinates the dominant `{y ≥ 0 : y ≥ x ∈ P}` can have facets with more nonzero coefficients
than `dim(P) + 1`. -/
theorem facet_support_bound_v2 {n : ℕ} (P : Set (Fin n → ℝ))
    (hPoly : ∃ V : Finset (Fin n → ℝ), P = convexHull ℝ (V : Set (Fin n → ℝ)))
    (hcube : P ⊆ UnitCube n) (pi : Fin n → ℝ) (beta : ℝ)
    (hfacet : IsFacet (Dominant P) ({x ∈ Dominant P | dotProduct pi x = beta})) :
    ((Finset.univ.filter (fun j => pi j ≠ 0)).card : ℤ) ≤ PolyDim P + 1 := by sorry

end Disjunctive.Dominants
