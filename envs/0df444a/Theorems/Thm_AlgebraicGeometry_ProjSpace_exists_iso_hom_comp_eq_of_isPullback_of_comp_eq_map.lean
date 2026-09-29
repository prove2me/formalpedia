-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
-- name    : AlgebraicGeometry.ProjSpace.exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/ba877a7e-ba31-596d-be20-f4c80e28b30c
-- title:
--   Uniqueness of base-change realisations inside Pⁿ_B
-- statement:
--   Fix $n \in \mathbb{N}$, commutative rings $A$ and $B$ with $B$ an $A$-algebra, and write $\mathbb{P}^n_A = \operatorname{Proj}$ of the graded ring of homogeneous components of $A[x_0,\dots,x_n]$ (the submodules `MvPolynomial.homogeneousSubmodule (Fin (n+1)) A`), with `ProjSpace.π A n : \mathbb{P}^n_A \to \operatorname{Spec} A` its structure morphism and `ProjSpace.map A B n : \mathbb{P}^n_B \to \mathbb{P}^n_A` the morphism obtained by applying `Proj.map` to the graded ring homomorphism given by coefficientwise base change `MvPolynomial.map (algebraMap A B)`. Let $Z$ be a scheme and $\iota : Z \to \mathbb{P}^n_A$ a morphism. Suppose given, for $j = 1, 2$, a scheme $Z_j$, a morphism $\iota_j : Z_j \to \mathbb{P}^n_B$ and a morphism $e_j : Z_j \to Z$ such that the square with sides $e_j : Z_j \to Z$ and $\iota_j$ followed by `ProjSpace.π B n` $: Z_j \to \operatorname{Spec} B$, over the cospan formed by $\iota$ followed by `ProjSpace.π A n` and by $\operatorname{Spec}$ of $A \to B$, is a pullback square, and such that $\iota \circ e_j = (\mathtt{ProjSpace.map}\ A\ B\ n) \circ \iota_j$. Then there exists an isomorphism $\varphi : Z_1 \cong Z_2$ with $\iota_2 \circ \varphi = \iota_1$ and $e_2 \circ \varphi = e_1$. No hypothesis of closed immersion or of flatness is imposed on $\iota$ or the $\iota_j$.
--
--   This is the uniqueness, up to a unique compatible isomorphism, of a realisation of the base change $Z \times_{\operatorname{Spec} A} \operatorname{Spec} B$ as a scheme sitting over $\mathbb{P}^n_B$ compatibly with $\iota$. It is used in the construction of the Hilbert functor and its representing scheme, where a closed subscheme of $\mathbb{P}^n_A$ has to be transported along $A \to B$ coherently.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
    (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (Z : Scheme.{0})
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (Z₁ : Scheme.{0}) (ι₁ : Z₁ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (e₁ : Z₁ ⟶ Z)
    (h₁ : IsPullback e₁ (ι₁ ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (h₁' : e₁ ≫ ι = ι₁ ≫ ProjSpace.map A B n)
    (Z₂ : Scheme.{0}) (ι₂ : Z₂ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (e₂ : Z₂ ⟶ Z)
    (h₂ : IsPullback e₂ (ι₂ ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (h₂' : e₂ ≫ ι = ι₂ ≫ ProjSpace.map A B n) :
    ∃ φ : Z₁ ≅ Z₂, φ.hom ≫ ι₂ = ι₁ ∧ φ.hom ≫ e₂ = e₁ := by sorry
