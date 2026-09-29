-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_orderedAffineCover_card_eq_of_isAffineHom_of_topologicalKrullDim_lt
-- name    : AlgebraicGeometry.exists_orderedAffineCover_card_eq_of_isAffineHom_of_topologicalKrullDim_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/0435ea6c-b5a6-5ae9-b76e-e36550d79c89
-- title:
--   Dimension <n and affine over P^N implies n affine charts
-- statement:
--   Let $k$ be an infinite field, $N$ a natural number, and let $X$ be a scheme whose underlying topological space is Noetherian. Let $\varphi : X \to \operatorname{Proj} k[x_0,\dots,x_N]$ be a morphism to the Proj of the graded ring $k[x_0,\dots,x_N]$ graded by total degree (the homogeneous submodules `MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k`), and assume $\varphi$ is an affine morphism. Let $n$ be a natural number with $\dim X < n$, the dimension being the topological Krull dimension, i.e. the supremum of lengths of chains of irreducible closed subsets of the underlying space. The conclusion asserts the existence of an ordered affine cover $\mathcal{K}$ of $X$, that is, a finite linearly ordered index type $\mathcal{K}.\iota$ together with opens $\mathcal{K}.U_i \subseteq X$ which are affine opens and satisfy $\bigsqcup_i \mathcal{K}.U_i = \top$, such that the index type has exactly $n$ elements and such that for every index $i$ there is a homogeneous polynomial $\ell$ of degree $1$ in $k[x_0,\dots,x_N]$ with $\mathcal{K}.U_i$ equal to the preimage under $\varphi$ of the basic open $D_+(\ell) \subseteq \operatorname{Proj} k[x_0,\dots,x_N]$.
--
--   This is the classical statement that a scheme affine over projective space over an infinite field, of dimension less than $n$, is covered by $n$ affine opens, each the preimage of the complement of a hyperplane. It feeds the alternating Čech computation of cohomology on a cover with few charts, and is used in the construction of the abelian-scheme property bundle via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_orderedAffineCover_card_eq`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_orderedAffineCover_card_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_orderedAffineCover_card_eq_of_isAffineHom_of_topologicalKrullDim_lt.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_orderedAffineCover_card_eq_of_isAffineHom_of_topologicalKrullDim_lt
    {k : Type u} [Field k] [Infinite k] {N : ℕ} {X : Scheme.{u}} [NoetherianSpace X]
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)) [IsAffineHom φ]
    {n : ℕ} (hdim : topologicalKrullDim X < n) :
    ∃ 𝒦 : X.OrderedAffineCover, Fintype.card 𝒦.ι = n ∧
      ∀ i : 𝒦.ι, ∃ ℓ : MvPolynomial (Fin (N + 1)) k,
        ℓ ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1 ∧
        𝒦.U i = φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) ℓ := by sorry
