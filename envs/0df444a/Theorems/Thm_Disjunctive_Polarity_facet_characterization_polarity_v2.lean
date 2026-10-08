-- Prove2me | Theorems.Thm_Disjunctive_Polarity_facet_characterization_polarity_v2
-- name    : Disjunctive.Polarity.facet_characterization_polarity_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:13.00073+00:00
-- url     : https://prove2.me/theorems/b340922e-2866-420b-ab12-325c6a87cc98
-- title:
--   Theorem 2.18 — facets of $\mathrm{cl\,conv}(F)$ are the extreme rays of $W_0$
-- statement:
--   This is Theorem 2.18 of Balas's *Disjunctive Programming*, the culminating result of Chapter 2: the facets of the closed convex hull of a union of polyhedra are exactly the extreme rays of the explicit cone $W_0$.
--
--   Let $P_h := \{x \in \mathbb{R}^n : A_h x \ge b_h\}$ ($h \in Q$), $F := \bigcup_{h\in Q} P_h$, $Q^* := \{h : P_h \ne \emptyset\}$, and
--   $$
--   W_0 := \{(\alpha, \alpha_0) : \exists\, u_h \ge 0\ (h \in Q^*),\ \alpha = u_h A_h,\ \alpha_0 \le u_h b_h\ \ \forall h \in Q^*\}.
--   $$
--   Assume $F$ is full-dimensional, $\dim F = n$. Then for $\alpha \ne 0$ and $\alpha_0 \ne 0$:
--   $$
--   \alpha x \ge \alpha_0 \text{ defines a facet of } \mathrm{cl\,conv}(F) \iff (\alpha, \alpha_0) \text{ is an extreme ray of } W_0,
--   $$
--   where "$\alpha x \ge \alpha_0$ defines a facet" means that the inequality is valid for $\mathrm{cl\,conv}(F)$ and $\mathrm{cl\,conv}(F) \cap \{x : \alpha x = \alpha_0\}$ is a facet of $\mathrm{cl\,conv}(F)$.
--
--   **Formalization Note.** The retired version expressed "defines a facet" by `IsFacet` applied to $\mathrm{cl\,conv}(F) \cap \{\alpha x = \alpha_0\}$, which does not say on which side of the hyperplane $\mathrm{cl\,conv}(F)$ lies; it was refuted by $F = [0,1]$, $\alpha = 1$, $\alpha_0 = 1$ ($x \le 1$, not $x \ge 1$, is the valid facet inequality). The new predicate `DefinesFacetGE` (module `Disjunctive_Polarity_FacetDefining`) adds validity of $\alpha x \ge \alpha_0$. The hypothesis $\alpha \neq 0$ is made explicit: an inequality $\alpha x \ge \alpha_0$ in the book's sense has a nonzero normal, and without it the statement fails, since for $F = [0,\infty) \subseteq \mathbb{R}$ the cone $W_0 = \{\alpha \ge 0,\ \alpha_0 \le 0\}$ has the extreme ray $(0,-1)$, while $0 \cdot x \ge -1$ defines no facet. With $\alpha \ne 0$ the statement is the standard fact that $W_0$ is the cone of valid inequalities of the full-dimensional polyhedron $\mathrm{cl\,conv}(F)$ (Theorem 1.2 / Corollary 2.17), whose extreme rays are its facet inequalities and possibly $(0,-1)$. Full-dimensionality is `PolyDim F = n` (affine hull of $F$ is $\mathbb{R}^n$).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §2.4, p. 36, Theorem 2.18 (cf. Balas 2005 survey, Thm 5.4) — with the implicit nonzero-normal condition α ≠ 0 made explicit

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_Polars
import Definitions.Def_Disjunctive_Polarity_FacetDefining

namespace Disjunctive.Polarity

/-- Theorem 2.18 (Balas, *Disjunctive Programming*, Springer 2018, §2.4, p. 36): let the
disjunctive set `F = ⋃_{h ∈ Q} P_h` be full-dimensional (`dim F = n`). Then for `α ≠ 0` and
`α₀ ≠ 0`, the inequality `α x ≥ α₀` defines a facet of `cl conv F` (it is valid for `cl conv F`
and cuts out a facet of it) if and only if `(α, α₀)` is an extreme ray of the cone `W₀`.

Version 2: (a) "defines a facet" now includes validity of `α x ≥ α₀` (`DefinesFacetGE`); the
retired `IsFacet` condition also accepted the reversed inequality `α x ≤ α₀` (`[0,1]`, `α = 1`,
`α₀ = 1`). (b) `α ≠ 0` is made explicit: for `F = [0, ∞) ⊆ ℝ`, `W₀ = {α ≥ 0, α₀ ≤ 0}` has the
extreme ray `(0, -1)`, which defines no facet; an inequality `α x ≥ α₀` in the book's sense has a
nonzero normal. -/
theorem facet_characterization_polarity_v2 {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (hdim : PolyDim (DisjunctiveSet m A b) = (n : ℤ)) (α : Fin n → ℝ) (α0 : ℝ)
    (hα : α ≠ 0) (hα0 : α0 ≠ 0) :
    DefinesFacetGE (closure (convexHull ℝ (DisjunctiveSet m A b))) α α0 ↔
      IsExtremeRay (W0 m A b) (α, α0) := by sorry

end Disjunctive.Polarity
