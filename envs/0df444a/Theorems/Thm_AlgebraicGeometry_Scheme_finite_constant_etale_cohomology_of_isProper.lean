-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_constant_etale_cohomology_of_isProper
-- name    : AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-18T22:18:14.361326+00:00
-- url     : https://prove2.me/theorems/30297275-95aa-455a-b4f8-6ce72c1479b2
-- title:
--   Proper étale cohomology with finite constant coefficients
-- statement:
--   Let $K$ be a separably closed field and $X$ a proper $K$-scheme. For any finite abelian group $A$, let $\underline A$ be its constant sheaf on the small étale site of $X$. For each $q\geq 0$, the group
--
--   $$H^q_{\mathrm{et}}(X,\underline A)$$
--
--   is finite. This is the finite constant coefficient case of the proper finiteness theorem.
-- source:
--   SGA 4, Exposé XIV, Corollaire 1.2, https://grothendiecksga.com/read/sga4/en/XIV-1.html.

import Mathlib

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_of_isProper
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (A : AddCommGrpCat.{u}) [Finite A] (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj A).H q) := by sorry
