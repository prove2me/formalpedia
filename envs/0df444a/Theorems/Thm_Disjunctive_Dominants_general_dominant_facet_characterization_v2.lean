-- Prove2me | Theorems.Thm_Disjunctive_Dominants_general_dominant_facet_characterization_v2
-- name    : Disjunctive.Dominants.general_dominant_facet_characterization_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:38.805981+00:00
-- url     : https://prove2.me/theorems/6e9beebc-ba9b-4b97-89bc-b0dc7e3ec95c
-- title:
--   Theorem 13.7 — the facets of the dominant of an arbitrary polytope $P\subseteq[0,1]^n$
-- statement:
--   This is Theorem 13.7 of Balas's *Disjunctive Programming*, the goal theorem of the mission: a complete, facet-exact description of the dominant of an arbitrary polytope, not necessarily upper monotone.
--
--   Let $P \subseteq [0,1]^n$ be a nonempty polytope and $P^+ := \{y\ge0 : y\ge x \text{ for some } x\in P\}$ its dominant. For $S\subseteq N$ let $P^S$ be the projection of $P$ onto the coordinates in $S$, and let $I^S$ be the set of inequalities $\pi x \ge 1$ that are valid for $P^S$, have $\pi_j>0$ exactly for $j\in S$, and hold with equality at $|S|$ linearly independent points of $P^S$. Then
--   $$
--   P^+ = \{x\ge0 : \pi x\ge1 \text{ for every } S\subseteq N \text{ and } \pi\in I^S\},
--   $$
--   and every one of these inequalities defines a facet of $P^+$.
--
--   **Formalization Note.** The retired version took $P$ to be an arbitrary nonempty subset of $\mathbb R^n$. A non-convex $P$, e.g. $\{e_1,e_2\}$, has a non-convex dominant, which no system of linear inequalities describes. The new statement requires, as the book does, that $P$ be a polytope: the convex hull of a finite set (hypothesis `hPoly`) contained in $[0,1]^n$ (`hcube`). Nonemptiness is kept, since for $P=\emptyset$ the dominant is empty. The definitions of $P^+$, $P^S$, $I^S$ (`IsInIS`, with linear independence of the $S$-coordinates) and of a facet are unchanged.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §13.2, p. 219-220, Theorem 13.7

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

namespace Disjunctive.Dominants

/-- Theorem 13.7 (Balas, *Disjunctive Programming*, Springer 2018, §13.2, p. 219-220), the goal
theorem of the mission: for an arbitrary nonempty polytope `P ⊆ [0,1]ⁿ` (not necessarily upper
monotone), `P⁺ = {x ≥ 0 : πx ≥ 1 for every S ⊆ N and π ∈ I^S}`, and every one of these
inequalities is facet-defining for `P⁺`.

Correction w.r.t. the retired version: `P` was an arbitrary set; it is now a polytope (the convex
hull of a finite point set, hypothesis `hPoly`) contained in the unit cube (`hcube`), as in the
book. A non-convex `P` has a non-convex dominant, which no system of linear inequalities can
describe. -/
theorem general_dominant_facet_characterization_v2 {n : ℕ} (P : Set (Fin n → ℝ))
    (hPoly : ∃ V : Finset (Fin n → ℝ), P = convexHull ℝ (V : Set (Fin n → ℝ)))
    (hcube : P ⊆ UnitCube n) (hP : P.Nonempty) :
    Dominant P = {x | 0 ≤ x ∧ ∀ (S : Finset (Fin n)) (pi : Fin n → ℝ), IsInIS S P pi →
        1 ≤ dotProduct pi x} ∧
      ∀ (S : Finset (Fin n)) (pi : Fin n → ℝ), IsInIS S P pi →
        IsFacet (Dominant P) ({x ∈ Dominant P | dotProduct pi x = 1}) := by sorry

end Disjunctive.Dominants
