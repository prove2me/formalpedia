-- Prove2me | Theorems.Thm_Disjunctive_Polarity_facet_characterization_via_transform
-- name    : Disjunctive.Polarity.facet_characterization_via_transform
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:19:17.52577+00:00
-- url     : https://prove2.me/theorems/402f53bb-69dd-45c0-85ac-bd8d6f43b0c6
-- title:
--   Proposition 2.11 — facets via a transformed projection cone
-- statement:
--   This is Proposition 2.11 of Balas's *Disjunctive Programming*, cited from [14]: unlike
--   Theorem 2.5's extreme rays of $W$ (which may give redundant inequalities), a specific
--   transformation of $Q$ yields a projection cone $\tilde W$ whose extreme rays are always facet
--   defining.
--
--   If $\mathrm{Proj}_x(Q)$ is full-dimensional, the inequality $vx \le v_0$ defines a facet of
--   $\mathrm{Proj}_x(Q)$ if and only if $(v,v_0)$ is an extreme ray of
--   $\mathrm{Proj}_{(v,v_0)}(\tilde W)$, where $\tilde W$ is the projection cone of the transformed
--   polyhedron $\tilde Q$ (obtained from $Q$ by replacing the coefficient matrix $B$ of $x$ with the
--   identity — a construction cited from [14], not re-derived here) and $w$ is the auxiliary variable
--   vector that transformation introduces.
--
--   **Formalization Note.** Following the book's own citation-based treatment, $\tilde W$ is taken as
--   given data (`Wt`) together with its defining relationship to $\mathrm{Proj}_x(Q)$ (`hRepr`,
--   transcribing the displayed formula for $\mathrm{Proj}_x(\tilde Q) = \mathrm{Proj}_x(Q)$ on p. 32)
--   rather than re-constructed from the transformation itself, which the book also does not carry out
--   in this chapter.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 32, Proposition 2.11

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_Transform

namespace Disjunctive.Polarity

/-- Proposition 2.11 ([14], Balas §2.3, p. 32): if `Proj_x(Q)` is full-dimensional, `vx ≤ v0`
defines a facet of `Proj_x(Q)` if and only if `(v,v0)` is an extreme ray of `Proj_{(v,v0)}(W̃)`,
where `W̃` is the projection cone of the transformed system `Q̃` obtained from `Q` by replacing
`B` with the identity. The transformation is cited from [14] and not spelled out on the page, so
`W̃` is carried by the properties the page states for it: a pointed convex cone whose *extreme
rays* give the representation `Proj_x(Q̃) = {x : vx ≤ v0 for all (v,w,v0) ∈ extr W̃}`, with
`Proj_x(Q̃) = Proj_x(Q)`. Quantifying instead over an arbitrary set satisfying a representation
by all of `Proj_{(v,v0)}(W̃)` makes the statement false: a finite generating set of valid
inequalities represents `Proj_x(Q)` and has no extreme rays at all. -/
theorem facet_characterization_via_transform {m p q w : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (Wt : Set ((Fin q → ℝ) × (Fin w → ℝ) × ℝ))
    (hFullDim : PolyDim (ProjOntoX (Poly2 A B b)) = (q : ℤ))
    (hWt_convex : Convex ℝ Wt)
    (hWt_cone : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ Wt, t • z ∈ Wt)
    (hWt_pointed : ∀ z ∈ Wt, -z ∈ Wt → z = 0)
    (hRepr : ProjOntoX (Poly2 A B b) =
      {x | ∀ v ww v0, IsExtremeRay Wt (v, ww, v0) → dotProduct v x ≤ v0})
    (v : Fin q → ℝ) (v0 : ℝ) :
    IsFacet (ProjOntoX (Poly2 A B b))
        (ProjOntoX (Poly2 A B b) ∩ {x | dotProduct v x = v0}) ↔
      IsExtremeRay (ProjVW Wt) (v, v0) := by sorry

end Disjunctive.Polarity
