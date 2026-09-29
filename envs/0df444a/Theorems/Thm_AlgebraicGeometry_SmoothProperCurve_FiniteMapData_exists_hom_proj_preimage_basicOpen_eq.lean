-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_hom_proj_preimage_basicOpen_eq
-- name    : AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_hom_proj_preimage_basicOpen_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/d0b154f8-4277-5a7d-99bd-dbca9d11c4e3
-- title:
--   Gluing a finite-map datum to a morphism C → P¹_R
-- statement:
--   Let $R$ be a commutative ring, let $c \colon C \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $\mathfrak{F}$ be a finite-map datum for $(c,\varepsilon)$: affine opens $U, V \subseteq C$ with $U \sqcup V = \top$, sections $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$, a natural number $m$, such that $U$ is exactly the complement of the set-theoretic image of $\varepsilon$, such that $U \cap V$ equals both the basic open $C_f$ and the basic open $C_g$, the restrictions of $f$ and $g$ to $U \cap V$ multiply to $1$, the $R$-algebra maps $R[T] \to \Gamma(C,U)$, $T \mapsto f$, and $R[T] \to \Gamma(C,V)$, $T \mapsto g$ (for the $R$-algebra structures induced by $c$) are finite, and for every local $R$-algebra $S$ and every $s \in S$ the quotient $(S \otimes_R \Gamma(C,U))/(1 \otimes f - s \otimes 1)$ is a finite free $S$-module of rank $m$. Then there exists a morphism $\pi \colon C \to \operatorname{Proj} R[x_0,x_1] = \mathbb{P}^1_R$, together with equalities $\pi^{-1}D_+(x_0) = U$ and $\pi^{-1}D_+(x_1) = V$ of opens of $C$, such that $\pi$ followed by the structure morphism $\mathbb{P}^1_R \to \operatorname{Spec} R$ is $c$, and such that the induced maps on sections carry the degree-zero element $x_1/x_0$ of the homogeneous localisation away from $x_0$ to $f$, and $x_0/x_1$ away from $x_1$ to $g$.
--
--   This is the classical construction of a morphism to projective space from a pair of charts with mutually inverse coordinates, specialised to $\mathbb{P}^1$: it converts the chart-wise record $\mathfrak{F}$ of a degree-$m$ map $C \to \mathbb{P}^1_R$ with poles only along $\varepsilon$ into an actual morphism of $R$-schemes with the prescribed chart preimages and coordinates. It is used in the further study of affine opens of $C$ lying over affine opens of $\mathbb{P}^1_R$, in particular by [`AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_isAffineOpen_le_preimage_of_finset`](thm.html#AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_isAffineOpen_le_preimage_of_finset).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_hom_proj_preimage_basicOpen_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_hom_proj_preimage_basicOpen_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε) :
    ∃ (π : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
      (hU : π ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0) = 𝔉.U)
      (hV : π ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1) = 𝔉.V),
      π ≫ ProjSpace.π R 1 = c ∧
      (π.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0)) 𝔉.U hU.ge).hom
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0)).hom (ProjSpace.ratio R 1 0 1)) = 𝔉.f ∧
      (π.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1)) 𝔉.V hV.ge).hom
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1)).hom (ProjSpace.ratio R 1 1 0)) = 𝔉.g := by sorry
