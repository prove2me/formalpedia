-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist
-- name    : AlgebraicGeometry.ProjSpace.exists_twistObj_top_forall_res_eq_of_mem_H0_twist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/847f75a0-af75-5620-b112-82201db7f6e7
-- title:
--   Čech 0-cocycles on the pulled-back standard charts glue
-- statement:
--   Let $A$ be a commutative ring, $n$ a natural number, $Z$ a scheme and $\varphi : Z \to \operatorname{Proj}$ of the graded ring of homogeneous polynomials in $x_0,\dots,x_n$ over $A$ (that is, $Z \to \mathbb{P}^n_A$) an affine morphism, and let $m$ be a natural number. Consider the $A$-module presheaf `ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m` on $Z$, whose sections over an open $U$ are the objects of `ProjSpace.twistObj (φ ≫ ProjSpace.π A n) φ m U`: families $(g_i)_{i \in \mathrm{Fin}(n+1)}$ with $g_i \in \Gamma(Z, U \sqcap \mathrm{pullbackChart}\,\varphi\,i)$ satisfying the compatibility predicate `TwistCompat φ m U`, with restriction maps `res`. Let `ProjSpace.stdCoverPullback φ` be the ordered affine cover of $Z$ indexed by $\mathrm{Fin}(n+1)$ whose $j$-th member is $\varphi^{-1}D_+(x_j)$, affine since $\varphi$ is affine. Let $c$ be a $0$-cochain for this cover, i.e. an assignment to each strictly monotone $s : \mathrm{Fin}\,1 \to \mathrm{Fin}(n+1)$ of a section of the twist over the corresponding intersection $\mathrm{inter}\,s$, and assume $c$ lies in the kernel $H^0$ of the degree-$0$ Čech differential. Then there is a section $g$ of the twist over $\top$ whose restriction along $\mathrm{inter}\,s \le \top$ equals $c\,s$ for every such $s$.
--
--   This is the gluing step identifying Čech $0$-cocycles for the pulled-back standard cover of $\mathbb{P}^n_A$ with global sections of the twisting datum $\varphi^*\mathcal{O}(m)$ on $Z$. It feeds the computation of global sections of $\mathcal{O}(m)$ along a closed immersion, namely [`AlgebraicGeometry.ProjSpace.exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion`](thm.html#AlgebraicGeometry.ProjSpace.exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_twistObj_top_forall_res_eq_of_mem_H0_twist
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom φ] (m : ℕ)
    (c : (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).cochain (ProjSpace.stdCoverPullback φ) 0)
    (hc : c ∈ (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).H0 (ProjSpace.stdCoverPullback φ)) :
    ∃ g : ProjSpace.twistObj (φ ≫ ProjSpace.π A n) φ m ⊤,
      ∀ s : (ProjSpace.stdCoverPullback φ).Idx 0,
        (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).res (le_top : (ProjSpace.stdCoverPullback φ).inter s ≤ ⊤) g = c s := by sorry
