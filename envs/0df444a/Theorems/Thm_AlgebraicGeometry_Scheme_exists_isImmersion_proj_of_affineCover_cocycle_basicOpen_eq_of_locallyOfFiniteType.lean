-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
-- name    : AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/e5220eb4-1219-56f1-bec6-6c56bb8fe552
-- title:
--   Ample chart datum yields an immersion into projective space
-- statement:
--   Let $B$ be a commutative ring, let $Y$ be a scheme and let $\pi_Y : Y \to \operatorname{Spec} B$ be a morphism that is locally of finite type. Suppose given $r \in \mathbb{N}$ and open subsets $V_i \subseteq Y$ for $i \in \mathrm{Fin}\,r$, each an affine open, with $\bigsqcup_i V_i = \top$, together with sections $w_{ij} \in \Gamma(Y, V_i)$ for all $i, j$ satisfying: $w_{ii} = 1$ for every $i$; for all $i, j, k$ the restriction of $w_{ik}$ to $V_i \cap V_j$ equals the product of the restriction of $w_{ij}$ from $V_i$ and the restriction of $w_{jk}$ from $V_j$; and for all $i, j$ the basic open subset $Y_{w_{ij}} \subseteq V_i$ equals $V_i \cap V_j$. The conclusion asserts the existence of a natural number $n$ and a morphism $\iota : Y \to \operatorname{Proj}$ of the graded ring $\bigoplus_d$ (homogeneous polynomials of degree $d$) in $n+1$ variables over $B$, i.e. into $\mathbb{P}^n_B$, such that $\iota$ is an immersion (`IsImmersion`) and $\iota$ followed by the structure morphism `ProjSpace.π B n` to $\operatorname{Spec} B$ equals $\pi_Y$.
--
--   This is the classical criterion that a quasi-compact scheme of finite type over an affine base carrying an ample invertible sheaf — here encoded concretely by a finite affine cover together with a unit cocycle $(w_{ij})$ whose non-vanishing loci are exactly the pairwise intersections — is quasi-projective over that base (EGA II 4.5.2, 5.3.2; Hartshorne II.7.6). It is used, via a passage from quotients and finite morphisms, in the construction of immersions of schemes into projective space over a Noetherian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
    (B : Type) [CommRing B] (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType πY]
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw2 : ∀ i j k : Fin r,
      Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j) :
    ∃ (qpn : ℕ) (qpι : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) B)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpn = πY := by sorry
