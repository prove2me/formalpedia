-- Prove2me | Theorems.Thm_Disjunctive_GeneralDisjunctions_corner_polyhedron_vertex_cut_off
-- name    : Disjunctive.GeneralDisjunctions.corner_polyhedron_vertex_cut_off
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:00:02.793108+00:00
-- url     : https://prove2.me/theorems/3b1d52b3-e2ce-4807-93b1-856a56570338
-- title:
--   Corollary 11.3 — every excluded corner-polyhedron vertex is cut off
-- statement:
--   This is Corollary 11.3 of Balas's *Disjunctive Programming*, the vertex-level restatement of
--   the goal theorem immediately following it in the text: **every vertex of a corner polyhedron
--   not in the integer hull is cut off by some standard intersection cut.**
--
--   Let $v$ be a vertex (extreme point) of a corner polyhedron $\mathrm{corner}(J)$ — the convex
--   hull of the integer points inside the LP cone $C(J)$ — with $v \notin \mathrm{conv}(P_I)$.
--   Then there is a basic solution structure ($I', J'$, tableau $\bar a'$) presenting $v$ itself
--   as a basic solution, and a $P_I$-free convex set $S$ with $v \in \mathrm{int}\,S$: exactly the
--   hypotheses from which Theorem 1.1 produces a standard intersection cut cutting off $v$.
--
--   The book states this corollary without proof, as an immediate consequence of Theorem 11.2's
--   completeness result combined with the containment $C(J) \supset \mathrm{corner}(J) \supset
--   \mathrm{conv}(P_I)$ established in Chapter 1.
--
--   **Formalization Note.** "Cut off by some SIC" is formalized as the existence of a basic-solution
--   presentation of $v$ together with a $P_I$-free $S$ containing $v$ in its interior — the exact
--   combination of hypotheses Theorem 1.1 needs to produce a cut removing $v$ — rather than via a
--   separately re-derived cut inequality, since the book gives no proof to formalize here. The
--   fresh $(I',J',\bar a')$ triple is existentially quantified independently of $v$'s original
--   apex-defining $(I,J,\bar a)$, since $v$ need not coincide with the cone's apex $w$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 152, Corollary 11.3

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Basic
import Definitions.Def_Disjunctive_GeneralDisjunctions_Corner

namespace Disjunctive.GeneralDisjunctions

/-- Corollary 11.3 (Balas §11.2, p. 152): every vertex `v` of a corner polyhedron `corner(J)`
(apex `w`, basic index set `I`, cobasis `J`, integrality set `Nprime`) such that `v ∉ conv(P_I)`
is cut off by some standard intersection cut, i.e. `v` is itself a basic solution (for some fresh
basic/nonbasic pair `I',J'` and tableau `abar'`) lying in the interior of some `P_I`-free convex
set `S` **whose intersection cut is valid for `P_I` and cuts `v` off**. Without those two
clauses the statement is satisfied by `J' = ∅` and a small ball around `v`, and names no cut. -/
theorem corner_polyhedron_vertex_cut_off {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : Finset ι) (abar : ι → ι → ℝ) (w : ι → ℝ) (Nprime : Finset ι) (PI : Set (ι → ℝ))
    (v : ι → ℝ) (hv : v ∈ Set.extremePoints ℝ (cornerPolyhedron I J abar w Nprime))
    (hvPI : v ∉ convexHull ℝ PI) :
    ∃ (I' J' : Finset ι) (abar' : ι → ι → ℝ) (S : Set (ι → ℝ)) (lam : ι → ℝ),
      (∀ j ∈ J', v j = 0) ∧ PIFree S PI v ∧
        (∀ j ∈ J', IsGreatest {t : ℝ | v + t • extremeRay I' abar' j ∈ S} (lam j)) ∧
        PI ⊆ IntersectionCutSet J' lam ∧ v ∉ IntersectionCutSet J' lam := by sorry

end Disjunctive.GeneralDisjunctions
