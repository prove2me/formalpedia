-- Prove2me | Theorems.Thm_Disjunctive_Polarity_facet_characterization_polarity
-- name    : Disjunctive.Polarity.facet_characterization_polarity
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:23:28.349843+00:00
-- url     : https://prove2.me/theorems/306a616c-905b-48e7-b93d-71884dc50a1c
-- title:
--   Theorem 2.18 — facet characterization via polarity
-- statement:
--   This is Theorem 2.18 of Balas's *Disjunctive Programming*, the chapter's culminating result: a
--   complete characterization of the facets of $\mathrm{cl}\,\mathrm{conv}(F)$ via the extreme rays
--   of the cone $W_0$.
--
--   Let $F$ be a disjunctive set with $\dim(F) = n$ (full-dimensional). Then, for $\alpha_0 \ne 0$:
--
--   $$
--   \alpha x \ge \alpha_0 \text{ defines a facet of } \mathrm{cl}\,\mathrm{conv}(F) \iff
--   (\alpha,\alpha_0) \text{ is an extreme ray of } W_0.
--   $$
--
--   This converts the geometric question "which inequalities are facet-defining for the closed convex
--   hull of a union of polyhedra" into a purely algebraic one about extreme rays of the explicit cone
--   $W_0$ built from the disjuncts' own data $(A_h, b_h)_{h \in Q}$ — the practical payoff of the
--   whole chapter's polarity apparatus (Proposition 2.13 through Corollary 2.17), and the natural
--   counterpart, on the polarity side, to the lifting-and-projection characterization of Theorem 2.1.
--
--   **Formalization Note.** `IsFacet` is applied here directly to
--   $\mathrm{cl}\,\mathrm{conv}(F) \subseteq \mathbb{R}^n$ (not to a `Poly2`-shaped pair), using
--   `IsFacet`'s generic statement over any real vector space.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 36, Theorem 2.18

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_Polars

namespace Disjunctive.Polarity

/-- Theorem 2.18 (Balas §2.4, p. 36): when `F` is full-dimensional, the inequality `αx ≥ α₀`
(with `α₀ ≠ 0`) defines a facet of `cl conv F` if and only if `(α, α₀)` is an extreme ray of
`W₀`. -/
theorem facet_characterization_polarity {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (hdim : PolyDim (DisjunctiveSet m A b) = (n : ℤ)) (α : Fin n → ℝ) (α0 : ℝ) (hα0 : α0 ≠ 0) :
    IsFacet (closure (convexHull ℝ (DisjunctiveSet m A b)))
        (closure (convexHull ℝ (DisjunctiveSet m A b)) ∩ {x | dotProduct α x = α0}) ↔
      IsExtremeRay (W0 m A b) (α, α0) := by sorry

end Disjunctive.Polarity
