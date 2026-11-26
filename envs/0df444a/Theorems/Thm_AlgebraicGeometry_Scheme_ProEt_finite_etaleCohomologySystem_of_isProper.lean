-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_finite_etaleCohomologySystem_of_isProper
-- name    : AlgebraicGeometry.Scheme.ProEt.finite_etaleCohomologySystem_of_isProper
-- status  : Open
-- author  : @Idealson
-- created : 2026-11-26T12:56:23.626109+00:00
-- url     : https://prove2.me/theorems/b04ce8cf-74d1-46fa-b482-eb7e98bf0fa6
-- title:
--   SGA 4 XIV, Corollaire 1.2 — étale cohomology of $\mathbb{Z}/\ell^n$ on a proper scheme over a separably closed field is finite
-- statement:
--   Let $K$ be a separably closed field, $X$ a proper $K$-scheme, and $\ell$ a prime number. For all $m, n \ge 0$ the étale cohomology group
--
--   $$
--   H^m\bigl(X_{\text{ét}}, \mathbb Z/\ell^n\bigr)
--   $$
--
--   of the constant sheaf $\mathbb Z/\ell^n$ on the small étale site of $X$ is finite.
--
--   No condition relates $\ell$ to the characteristic of $K$. This is the special case, for constant coefficients, of the finiteness of the cohomology of constructible torsion sheaves on proper schemes over separably closed fields. In this mission it supplies the finiteness hypothesis under which $\ell$-adic cohomology is the inverse limit of the groups $H^m(X_{\text{ét}}, \mathbb Z/\ell^n)$.
--
--   **Formalization Note** The group is the value at $n$ of the inverse system `etaleCohomologySystem X ℓ m`, i.e. `Sheaf.H` of the constant sheaf with value `ULift (ZMod (ℓ ^ n))` in `Ab.{u + 1}` for $X$ a `Scheme.{u}` and $K$ a field in `Type u`. Primality of $\ell$ is assumed to match the goal; it excludes $\ell = 0$, for which $\mathbb Z/\ell^n = \mathbb Z$ and the statement fails.
-- source:
--   M. Artin, SGA 4, Exposé XIV, Théorème de finitude pour un morphisme propre, Corollaire 1.2, https://grothendiecksga.com/read/sga4/en/XIV-1.html, applied to the constant sheaves Z/l^n. Not a result of the Bhatt–Scholze paper: it is the input that makes the hypothesis of the mission goal hold in the situation of its Introduction (B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), p. 2).

import Mathlib
import Definitions.Def_ProEtale_Comparator_Definitions

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Limits Opposite Abelian
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt

theorem AlgebraicGeometry.Scheme.ProEt.finite_etaleCohomologySystem_of_isProper (K : Type u) [Field K] [IsSepClosed K] (X : Scheme.{u}) (π : X ⟶ Spec (.of K)) [IsProper π] (ℓ : ℕ) [Fact ℓ.Prime] (m n : ℕ) :
    Finite (ToType ((EllAdicEtaleComparison.etaleCohomologySystem X ℓ m).obj (op n))) := by sorry
