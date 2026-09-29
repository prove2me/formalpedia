-- Prove2me | Theorems.Thm_FamousTheorems_elliptic_curves_equal_j_isomorphic_7a
-- name    : FamousTheorems.elliptic_curves_equal_j_isomorphic_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:33.616853+00:00
-- url     : https://prove2.me/theorems/33d4f381-ee79-4a5e-949d-0b150a9223a0
-- title:
--   Elliptic curves over a separably closed field with equal j-invariant are isomorphic
-- statement:
--   **Elliptic curves with equal $j$-invariant are isomorphic over a separably closed field.** Let $F$ be a separably closed field and let $E,E'$ be elliptic curves over $F$ given by Weierstrass equations. If $j(E)=j(E')$, then there is a change of variables $x=u^2x'+r$, $y=u^3y'+su^2x'+t$ with $u\in F^\times$ that transforms $E$ into $E'$.
--
--   The $j$-invariant thus classifies elliptic curves up to isomorphism over a separably closed field, in particular over an algebraically closed field such as $\mathbb C$. Together with the existence of a curve for every value of $j$, this identifies the affine line with the coarse moduli space of elliptic curves. Over non-closed fields, curves with equal $j$ may be non-isomorphic twists.
--
--   **Formalization note.** Mathlib's `WeierstrassCurve.exists_variableChange_of_j_eq`. `WeierstrassCurve.VariableChange F` is the group of admissible changes of variables acting on Weierstrass curves, and `IsElliptic` says that the discriminant is a unit.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `WeierstrassCurve.exists_variableChange_of_j_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem elliptic_curves_equal_j_isomorphic_7a {F : Type*} [Field F] [IsSepClosed F] (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]
    (h : E.j = E'.j) : ∃ C : WeierstrassCurve.VariableChange F, C • E = E' := by sorry

end FamousTheorems
