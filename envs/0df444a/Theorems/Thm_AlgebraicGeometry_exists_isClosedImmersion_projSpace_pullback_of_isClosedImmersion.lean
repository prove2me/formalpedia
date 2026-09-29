-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
-- name    : AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/15fbefcf-89ea-5e7d-bf8e-af6412e75b66
-- title:
--   Relative Segre embedding for projective closed subschemes
-- statement:
--   Let $R$ be a commutative ring and let $f : X \to \operatorname{Spec} R$ and $g : Y \to \operatorname{Spec} R$ be morphisms of schemes, where $\operatorname{Spec} R$ means $\mathrm{Spec}$ of the commutative ring object `CommRingCat.of R`. Write $\mathbb{P}^n_R$ for $\mathrm{Proj}$ of the graded ring given by the homogeneous submodules of the polynomial ring $R[x_0,\dots,x_n]$ in the $n+1$ variables indexed by `Fin (n + 1)`, and let `ProjSpace.π R n` be the given morphism $\mathbb{P}^n_R \to \operatorname{Spec} R$ playing the role of its structure morphism. Assume given a natural number $N$ and a morphism $\iota_X : X \to \mathbb{P}^N_R$ which is a closed immersion and satisfies $\iota_X$ followed by `ProjSpace.π R N` equal to $f$, and likewise a natural number $M$ and a closed immersion $\iota_Y : Y \to \mathbb{P}^M_R$ with $\iota_Y$ followed by `ProjSpace.π R M` equal to $g$. The conclusion asserts the existence of a natural number $K$ and a morphism $\iota$ from the pullback $X \times_{\operatorname{Spec} R} Y$ of $f$ and $g$ to $\mathbb{P}^K_R$ such that $K + 1 = (N+1)(M+1)$, the morphism $\iota$ is a closed immersion, and $\iota$ followed by `ProjSpace.π R K` equals the first projection of the pullback followed by $f$, i.e. $\iota$ is a morphism over $\operatorname{Spec} R$ for the canonical structure morphism of the fibre product.
--
--   This is the relative Segre embedding: a fibre product over $\operatorname{Spec} R$ of two schemes projective over $R$, presented as closed subschemes of $\mathbb{P}^N_R$ and $\mathbb{P}^M_R$, is again projective over $R$, embedded in $\mathbb{P}^{(N+1)(M+1)-1}_R$. It serves as the closure property of the class of projectively embeddable $R$-schemes used when forming products and graphs, and is invoked by the results on immersions into projective space over finite free algebras, on adic thickenings of closed subschemes of $\mathbb{P}^n_R$, and on pullbacks of points of such subschemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R))
    (hιX : IsClosedImmersion ιX) (hιXf : ιX ≫ ProjSpace.π R N = f)
    (M : ℕ) (ιY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) R))
    (hιY : IsClosedImmersion ιY) (hιYg : ιY ≫ ProjSpace.π R M = g) :
    ∃ (K : ℕ) (ι : pullback f g ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (K + 1)) R)),
      K + 1 = (N + 1) * (M + 1) ∧ IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R K = pullback.fst f g ≫ f := by sorry
