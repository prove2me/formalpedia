-- Prove2me | Theorems.Thm_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle
-- name    : Algebra.FormallySmooth.exists_linearMap_eq_of_symmetric_hochschild_two_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/f97e27fb-e76f-56ae-96c0-7b3c6a02ba9d
-- title:
--   Symmetric normalised Hochschild 2-cocycles are coboundaries for formally smooth algebras
-- statement:
--   Let $R$ be a commutative ring and $S$ a commutative $R$-algebra which is formally smooth over $R$, and let $M$ be an abelian group carrying compatible $R$- and $S$-module structures (the $R$-action factoring through the $S$-action, i.e. a scalar tower $R \to S \to M$). Let $\psi \colon S \to S \to M$ be an $R$-bilinear map, assumed symmetric, $\psi(x,y) = \psi(y,x)$ for all $x, y \in S$; normalised, $\psi(1,y) = 0$ for all $y \in S$; and a Hochschild $2$-cocycle in the sense that $$x \cdot \psi(y,z) - \psi(xy,z) + \psi(x,yz) - z \cdot \psi(x,y) = 0$$ for all $x, y, z \in S$, the scalar multiplications being those of the $S$-module $M$. The conclusion is that $\psi$ is a coboundary: there exists an $R$-linear map $l \colon S \to M$ with $l(1) = 0$ such that $$\psi(x,y) = l(xy) - x \cdot l(y) - y \cdot l(x)$$ for all $x, y \in S$.
--
--   In cochain form this is the vanishing of the group of commutative infinitesimal extensions $\operatorname{Exalcomm}_R(S,M)$ (equivalently Harrison's second cohomology, or the first André–Quillen cohomology) of a formally smooth $R$-algebra: the symmetric normalised cocycle $\psi$ is the multiplication defect of the square-zero extension $S \oplus M$, and $l$ records an $R$-algebra section of it. It is used in the construction of multiplicative structures on deformations of curves, via [`AlgebraicCurve.exists_mul_eq_hochschild_coboundary_of_discr_ne_zero`](thm.html#AlgebraicCurve.exists_mul_eq_hochschild_coboundary_of_discr_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem Algebra.FormallySmooth.exists_linearMap_eq_of_symmetric_hochschild_two_cocycle
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (ψ : S →ₗ[R] S →ₗ[R] M)
    (hsymm : ∀ x y, ψ x y = ψ y x)
    (hone : ∀ y, ψ 1 y = 0)
    (hcoc : ∀ x y z, x • ψ y z - ψ (x * y) z + ψ x (y * z) - z • ψ x y = 0) :
    ∃ l : S →ₗ[R] M, l 1 = 0 ∧ ∀ x y, ψ x y = l (x * y) - x • l y - y • l x := by sorry
