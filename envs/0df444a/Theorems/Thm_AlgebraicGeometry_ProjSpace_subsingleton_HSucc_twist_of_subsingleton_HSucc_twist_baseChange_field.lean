-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_subsingleton_HSucc_twist_of_subsingleton_HSucc_twist_baseChange_field
-- name    : AlgebraicGeometry.ProjSpace.subsingleton_HSucc_twist_of_subsingleton_HSucc_twist_baseChange_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/1a7f0e75-466f-5629-a0fd-f1137b18d16d
-- title:
--   Čech vanishing for twists descends from a field extension
-- statement:
--   Let $k$ be a field, $n$ a natural number and $\iota : Z \to \operatorname{Proj}$ of the graded ring of homogeneous components of $k[X_0,\dots,X_n]$ an affine morphism from a scheme $Z$; let $K$ be a field equipped with a $k$-algebra structure and $\iota' : Z' \to \operatorname{Proj}$ of the corresponding graded ring over $K$ an affine morphism. Let $e : Z' \to Z$ be a morphism such that the square formed by $e$, the structure morphisms $\iota' \,\text{followed by}\, \pi_{K,n}$ and $\iota \,\text{followed by}\, \pi_{k,n}$ to $\operatorname{Spec} K$ and $\operatorname{Spec} k$, and $\operatorname{Spec}$ of $k \to K$ is a pullback square, and such that $e$ followed by $\iota$ equals $\iota'$ followed by `ProjSpace.map k K n`, the morphism $\operatorname{Proj}_K \to \operatorname{Proj}_k$ induced by coefficientwise base change of multivariable polynomials. Fix $d, i \in \mathbb{N}$. Consider the $\mathcal O$-module presheaf `ProjSpace.twist` of degree-$d$ twisted sections, whose value on an open $U$ consists of families of sections over $U$ intersected with the $j$-th pullback chart, $j \in \{0,\dots,n\}$, satisfying the predicate `TwistCompat`, together with the ordered affine cover `ProjSpace.stdCoverPullback` of $Z$ (resp. $Z'$) by the preimages under $\iota$ (resp. $\iota'$) of the standard basic opens $D(X_j)$. The assertion is: if the module $\ker d^{i+1} / (d^{i}\text{-image pulled back to } \ker d^{i+1})$ attached to these data over $K$ is a subsingleton, then so is the corresponding module over $k$; that is, vanishing of the $(i+1)$-st Čech cohomology of the twist on the standard cover descends from $Z'$ to $Z$.
--
--   This is the descent, along a field extension, of the vanishing of a higher Čech cohomology group of $\mathcal O_Z(d)$ computed on the pullback of the standard cover of projective space, for an arbitrary realisation of the base change of $Z \subseteq \mathbb P^n_k$ to $K$. It feeds the construction of the Hilbert function of a point, being used in [`AlgebraicGeometry.HilbertFunctor.exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf`](thm.html#AlgebraicGeometry.HilbertFunctor.exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_subsingleton_HSucc_twist_of_subsingleton_HSucc_twist_baseChange_field.lean

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

theorem AlgebraicGeometry.ProjSpace.subsingleton_HSucc_twist_of_subsingleton_HSucc_twist_baseChange_field
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom ι]
    (K : Type u) [Field K] [Algebra k K] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) [IsAffineHom ι']
    (e : Z' ⟶ Z)
    (hpb : IsPullback e (ι' ≫ ProjSpace.π K n) (ι ≫ ProjSpace.π k n) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hcomp : e ≫ ι = ι' ≫ ProjSpace.map k K n) (d i : ℕ)
    (hK : Subsingleton ((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).HSucc (ProjSpace.stdCoverPullback ι') i)) :
    Subsingleton ((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).HSucc (ProjSpace.stdCoverPullback ι) i) := by sorry
