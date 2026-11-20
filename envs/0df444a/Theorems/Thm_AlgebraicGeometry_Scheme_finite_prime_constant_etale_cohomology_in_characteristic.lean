-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_prime_constant_etale_cohomology_in_characteristic
-- name    : AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_in_characteristic
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-19T20:37:34.0954+00:00
-- url     : https://prove2.me/theorems/567ec6ed-0a00-4c57-9a13-6d69ebcfeb74
-- title:
--   Proper étale finiteness for prime coefficients in the characteristic
-- statement:
--   Let $K$ be a separably closed field, $X$ a proper $K$-scheme, and $p$ a prime. $K$ has characteristic $p$. For every $q\geq 0$ the group
--   $$H^q_{\mathrm{et}}(X,\underline{\mathbf Z/p\mathbf Z})$$
--   is finite. The coefficient sheaf is constant on the small étale site.
-- source:
--   SGA 4, tome 3, Exposé XIV, Corollaire 1.2, https://grothendiecksga.com/read/sga4/fr/XIV-1.html. For the Artin–Schreier argument over an algebraically closed field, see Stacks Project, Lemma 59.63.6, https://stacks.math.columbia.edu/tag/0A3P.

import Mathlib

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_in_characteristic
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (p : ℕ) (hp : p.Prime)
    (hK : (p : K) = 0) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod p)))).H q) := by sorry
