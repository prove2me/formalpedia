-- Prove2me | Theorems.Thm_FamousTheorems_elliptic_curve_point_group_law_7b
-- name    : FamousTheorems.elliptic_curve_point_group_law_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:37.952985+00:00
-- url     : https://prove2.me/theorems/1232659b-81fd-41f5-b4f4-21012eb18fda
-- title:
--   The points of an elliptic curve form an abelian group
-- statement:
--   **The points of an elliptic curve form an abelian group.** Let $E$ be a Weierstrass curve over a field $F$ and let $E(F)$ be its nonsingular $F$-points together with the point at infinity $O$. The chord–tangent addition law on $E(F)$ is associative and commutative, and every point $P$ has an inverse $-P$ with $P+(-P)=O$. So $E(F)$ is an abelian group with identity $O$.
--
--   The group law is at the heart of the arithmetic of elliptic curves: the Mordell–Weil theorem, the Birch and Swinnerton-Dyer conjecture, elliptic curve cryptography and Lenstra's factorization method are all about this group. Commutativity is clear from the construction, but associativity is not; classical proofs use the Cayley–Bacharach theorem or long computations. Mathlib identifies the group of points with the class group of the coordinate ring.
--
--   **Formalization note.** The group structure is Mathlib's instance `WeierstrassCurve.Affine.Point.instAddCommGroup`, and the statement records the associativity, commutativity and inverse laws of the addition on `W.Point`. For an elliptic curve every point of the curve is nonsingular, so `W.Point` is the usual group $E(F)$. The addition, zero and negation are the explicit chord–tangent formulas defined in Mathlib, so the statement is about that concrete operation.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `WeierstrassCurve.Affine.Point.instAddCommGroup`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem elliptic_curve_point_group_law_7b {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} (P Q R : W.Point) :
    P + Q + R = P + (Q + R) ∧ P + Q = Q + P ∧ P + -P = 0 := by sorry

end FamousTheorems
