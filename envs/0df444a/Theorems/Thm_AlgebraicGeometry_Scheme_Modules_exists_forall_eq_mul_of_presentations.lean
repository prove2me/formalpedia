-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations
-- name    : AlgebraicGeometry.Scheme.Modules.exists_forall_eq_mul_of_presentations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/0d5400b6-be5e-5b2c-964a-3c9eae42eb6d
-- title:
--   Two embeddings of a sheaf into K(X) differ by a rational function
-- statement:
--   Let $X$ be an integral scheme, $\mathcal M$ a sheaf of $\mathcal O_X$-modules on $X$ (an object of `X.Modules`), and $K(X)$ the function field of $X$. Given two families $\varphi = (\varphi_U)_U$ and $\varphi' = (\varphi'_U)_U$ of additive maps $\Gamma(\mathcal M, U) \to K(X)$, indexed by the open sets $U$ of $X$, assume: for all opens $V \le U$ with $V$ nonempty, $\varphi_V$ (respectively $\varphi'_V$) applied to the restriction along $V \le U$ of a section $m$ over $U$ equals $\varphi_U(m)$ (respectively $\varphi'_U(m)$); for every nonempty open $U$, every $a \in \Gamma(X, U)$ and every $m \in \Gamma(\mathcal M, U)$ one has $\varphi_U(a \cdot m) = \iota(a)\,\varphi_U(m)$ and likewise for $\varphi'$, where $\iota$ is the structure map $\Gamma(X, U) \to K(X)$; and $\varphi_U$ and $\varphi'_U$ are injective for every nonempty open $U$. Assume finally that $\mathcal M$ has a nonzero section over some open set. Then there exists $g \in K(X)$ with $g \ne 0$ such that $\varphi'_U(m) = g\,\varphi_U(m)$ for every nonempty open $U$ and every $m \in \Gamma(\mathcal M, U)$.
--
--   This is the uniqueness half of the classical statement that a torsion-free rank-one sheaf on an integral scheme embeds into the constant sheaf $K(X)$ uniquely up to multiplication by an element of $K(X)^\times$, so that two such presentations of an invertible sheaf differ by a rational function (and the associated divisors differ by a principal divisor). It is used in the project to compare divisors attached to invertible ideal sheaves and to identify images of invertible modules with partial Riemann–Roch spaces inside $K(X)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_forall_eq_mul_of_presentations
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules)
    (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hsec : ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0) :
    ∃ g : X.functionField, g ≠ 0 ∧ ∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m := by sorry
