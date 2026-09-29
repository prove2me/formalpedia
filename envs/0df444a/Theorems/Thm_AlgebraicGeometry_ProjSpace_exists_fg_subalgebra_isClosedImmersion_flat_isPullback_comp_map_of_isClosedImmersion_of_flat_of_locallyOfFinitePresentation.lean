-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.ProjSpace.exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/44445023-0444-5411-b136-0fd554f8e11d
-- title:
--   Noetherian approximation of flat closed subschemes of Pⁿ
-- statement:
--   Let $A$ be a commutative ring, $n$ a natural number, and write $\mathbb{P}^n_A$ for $\operatorname{Proj}$ of the graded ring of homogeneous components of $A[x_0,\dots,x_n]$, with structure morphism $\pi_{A,n} : \mathbb{P}^n_A \to \operatorname{Spec} A$. Let $Z$ be a scheme and $\iota : Z \to \mathbb{P}^n_A$ a morphism which is a closed immersion, and assume that the composite $\iota$ followed by $\pi_{A,n}$ is flat and locally of finite presentation. Then there is a subalgebra $A_0 \subseteq A$ over $\mathbb{Z}$ (that is, a subring of $A$) which is finitely generated as a $\mathbb{Z}$-algebra, a scheme $Z_0$, a morphism $\iota_0 : Z_0 \to \mathbb{P}^n_{A_0}$ and a morphism $g : Z \to Z_0$ such that: $\iota_0$ is a closed immersion; the composite $\iota_0$ followed by $\pi_{A_0,n}$ is flat and locally of finite presentation; the square with top edge $g$, left edge $\iota$ followed by $\pi_{A,n}$, right edge $\iota_0$ followed by $\pi_{A_0,n}$, and bottom edge $\operatorname{Spec}$ of the inclusion $A_0 \to A$ is cartesian; and $g$ is compatible with the embeddings, in the sense that $g$ followed by $\iota_0$ equals $\iota$ followed by the morphism $\mathbb{P}^n_A \to \mathbb{P}^n_{A_0}$ induced by the graded ring homomorphism $A_0[x_0,\dots,x_n] \to A[x_0,\dots,x_n]$.
--
--   This is the Noetherian approximation (limit) statement for flat, finitely presented closed subschemes of projective space, as in EGA IV: such a subscheme descends, together with its projective embedding, to a finitely generated subring of the base. It is used in the construction and analysis of the Hilbert functor, where it reduces statements about arbitrary base rings to the Noetherian case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
    {A : Type u} [CommRing A] (n : ℕ)
    (Z : Scheme.{u}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ ProjSpace.π A n))
    (hfp : LocallyOfFinitePresentation (ι ≫ ProjSpace.π A n)) :
    ∃ (A₀ : Subalgebra ℤ A), A₀.FG ∧
      ∃ (Z₀ : Scheme.{u}) (ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ↥A₀)) (g : Z ⟶ Z₀),
        IsClosedImmersion ι₀ ∧ Flat (ι₀ ≫ ProjSpace.π ↥A₀ n) ∧ LocallyOfFinitePresentation (ι₀ ≫ ProjSpace.π ↥A₀ n) ∧
        IsPullback g (ι ≫ ProjSpace.π A n) (ι₀ ≫ ProjSpace.π ↥A₀ n)
          (Spec.map (CommRingCat.ofHom (algebraMap ↥A₀ A))) ∧
        g ≫ ι₀ = ι ≫ ProjSpace.map ↥A₀ A n := by sorry
