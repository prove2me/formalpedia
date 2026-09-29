-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
-- name    : AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/4224ec27-e51a-54da-991e-688e7bd5bb57
-- title:
--   Prescribing the ratios x_k/xᵢ on the chart D₊(xᵢ)
-- statement:
--   Let $R$ be a commutative ring, $n$ a natural number and $i \in \{0,\dots,n\}$ (an element of `Fin (n+1)`), and let $B$ be a commutative $R$-algebra. Let $b : \{0,\dots,n\} \to B$ be a family of elements of $B$ with $b_i = 1$. Then there exists an $R$-algebra homomorphism $\varphi$ from `HomogeneousLocalization.Away` of the grading of $R[x_0,\dots,x_n]$ by the submodules of homogeneous polynomials at the element $x_i$ — that is, the degree-zero part of the localization of $R[x_0,\dots,x_n]$ at $x_i$, the coordinate ring of the standard chart $D_+(x_i) \subseteq \mathbb{P}^n_R$ — to $B$, such that for every $k \in \{0,\dots,n\}$ one has $\varphi(\mathrm{ratio}\,R\,n\,i\,k) = b_k$, where `ProjSpace.ratio R n i k` is the homogeneous localization element with numerator $x_k$ and denominator $x_i^{1}$, both homogeneous of degree one, i.e. $x_k/x_i$. Only existence of such a $\varphi$ is asserted; uniqueness is not part of the statement.
--
--   This is the mapping-out property of the standard affine chart $D_+(x_i)$ of $\mathbb{P}^n_R$: $R$-algebra maps out of its coordinate ring are obtained by prescribing the values of the ratios $x_k/x_i$, subject to the normalisation $x_i/x_i \mapsto 1$. It is used, together with the fact that the ratios generate the chart over $R$, to construct and compare morphisms into projective space, and is cited in the treatment of finite presentation and quasi-finiteness for presentations of modules over $\operatorname{Proj}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    {B : Type v} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1) :
    ∃ φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B,
      ∀ k, φ (ProjSpace.ratio R n i k) = b k := by sorry
