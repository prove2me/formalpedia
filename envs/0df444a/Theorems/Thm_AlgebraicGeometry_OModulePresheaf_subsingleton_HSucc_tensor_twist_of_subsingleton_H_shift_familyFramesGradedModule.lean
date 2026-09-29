-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
-- name    : AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/0d905e80-29cd-587c-876f-dfc89556c856
-- title:
--   Graded Čech vanishing transfers to twisted sheaf Čech vanishing
-- statement:
--   Let $A$ be a commutative ring, $r,s\in\mathbb N$, and $P$ a scheme equipped with an affine morphism $\iota : P \to \operatorname{Proj}$ of the homogeneous coordinate ring $A[x_0,\dots,x_r]$ (given as `MvPolynomial.homogeneousSubmodule (Fin (r+1)) A`) and a morphism $q : P \to \operatorname{Spec} A$. Let $G : \mathbb N \to$ `OModulePresheaf q` be a family of module data over $q$, each consisting of an $A$-module and $\Gamma(P,U)$-module $G_k(U)$ for every open $U$ together with compatible $A$-linear, semilinear restriction maps, and assume each $G_k$ satisfies `IsQuasicoherent`: for every affine open $U$ and $f \in \Gamma(P,U)$, every section over the basic open $P_f$ is $f^n$ times the restriction of a section over $U$ for some $n$, and a section over $U$ restricting to $0$ on $P_f$ is annihilated by some $f^n$. Let $\theta_m : G_k \to G_{k+1}$ ($m \in \operatorname{Fin} s$, $k\in\mathbb N$) be morphisms defined on affine opens (sectionwise $\Gamma$-semilinear and compatible with restriction), satisfying `YComm`, i.e. $\theta_m \circ \theta_{m'} = \theta_{m'} \circ \theta_m$ on sections over affine opens. Fix $d, k, i \in \mathbb N$. Form `familyFramesGradedModule ι G θ hθ`, the graded module over $A[y_1,\dots,y_s]$ in the $r+1$ variables $x_l$ whose underlying module is the frames module $\mathbb Z \times \mathbb N \times \operatorname{Fin}(r+1) \to$ sections of $G_k$ on the pulled-back chart $\iota^{-1}D_+(x_j)$, with degree pieces cut out by the homogeneity condition, with $x_l$ acting by $f \mapsto ((e,k,j) \mapsto u_{jl}\cdot f(e-1,k,j))$ for the frame units $u_{jl}$, and with the $y_m$ acting through $\theta_m$. Assume that the $(i+1)$-st cohomology `GradedModule.H … (i+1)` of the algebraic Čech complex of the degree shift of this graded module by $d$ is a subsingleton. Then the $(i+1)$-st Čech cohomology group `HSucc … i`, namely $\ker(d_{i+1})/\operatorname{im}(d_i)$, of the tensor product presheaf $G_k \otimes \mathcal O(d)$ (the twist datum `ProjSpace.twist q ι d`) relative to the ordered affine cover of $P$ by the preimages $\iota^{-1}D_+(x_j)$ is a subsingleton.
--
--   This is the transfer of vanishing from the purely algebraic Čech cohomology of the graded module of frames of the family $(G_k)$ to the geometric alternating Čech cohomology of an individual twist $G_k(d)$ on the pullback of the standard cover of $\mathbb P^r_A$, the comparison underlying the computation of cohomology of twisted quasi-coherent sheaves on projective space. It is used in deriving simultaneous vanishing for all $k$ and in the finiteness statement for tensor powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
    {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsAffineHom ι]
    {q : P ⟶ Spec (CommRingCat.of A)}
    (G : ℕ → OModulePresheaf q) (hq : ∀ k, (G k).IsQuasicoherent)
    {s : ℕ} (θ : Fin s → ∀ k : ℕ, OModulePresheaf.AffHom (G k) (G (k + 1))) (hθ : OModulePresheaf.YComm G θ)
    (d k i : ℕ)
    (hv : Subsingleton (ProjSpaceCech.GradedModule.H
      (ProjSpaceCech.GradedModule.shift (OModulePresheaf.familyFramesGradedModule ι G θ hθ) (d : ℤ)) (i + 1))) :
    Subsingleton (((G k).tensor (ProjSpace.twist q ι d)).HSucc (ProjSpace.stdCoverPullback ι) i) := by sorry
