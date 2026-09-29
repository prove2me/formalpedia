-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isFG_hom_injective_saturated_familyFramesGradedModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4c3bc899-7465-542a-aabc-510841c0f8bd
-- title:
--   Finite generation up to saturation of the frames graded module
-- statement:
--   Let $A$ be a commutative ring, $r\in\mathbb N$, and $P$ a scheme equipped with a closed immersion $\iota : P \to \operatorname{Proj} A[x_0,\dots ,x_r]$ and a morphism $q : P \to \operatorname{Spec} A$ with $\iota$ followed by the structure morphism $\mathrm{ProjSpace}.\pi$ equal to $q$. Let $G$ assign to each $k\in\mathbb N$ a presheaf of modules over $q$ (an $A$-module $(G\,k)(U)$ for every open $U\subseteq P$, also a $\Gamma(P,U)$-module compatibly, with semilinear functorial restrictions), each coherent, i.e. $(G\,k)(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and each quasi-coherent in the sense of the localisation condition on basic opens of affine opens. Let $s\in\mathbb N$ and, for each $m\in\mathrm{Fin}\,s$ and each $k$, let $\theta_{m,k} : G\,k \to G\,(k+1)$ be a morphism given on affine opens ($\Gamma$-linear maps commuting with restriction); assume `YComm`, that $\theta_{m,k+1}\circ\theta_{m',k} = \theta_{m',k+1}\circ\theta_{m,k}$ on sections over affine opens, and that for every $k$ and every affine open $U$ the ranges of the $\theta_{m,k}$ on $U$ span $(G\,(k+1))(U)$, i.e. their supremum is $\top$. Write $M =$ `familyFramesGradedModule` $\iota\,G\,\theta\,h_\theta$ for the graded module over $A[y_1,\dots ,y_s] = \mathrm{MvPolynomial}(\mathrm{Fin}\,s)\,A$ whose underlying module consists of the families $f(e,k,j)$ of sections over the pulled-back charts $\mathrm{ProjSpace.pullbackChart}\,\iota\,j$, with $f$ lying in degree $e$ when $f$ is concentrated in the single index $e$, vanishes if $e<0$, satisfies for $e\ge 0$ the transition predicate `FramesCompat` in degree $e$ for every $k$, and is nonzero for only finitely many $k$; the operators $x_l$ act by multiplying the $j$-th member by $\mathrm{ProjSpace.frameUnit}\,\iota\,j\,l$ with a shift of degree, and the $y_m$ act through the endomorphisms `yEnd` determined by the $\theta_m$. The assertion is that there exist a graded module $D$ over $A[y_1,\dots ,y_s]$ with $r+1$ commuting operators, a witness that $D$ is finitely generated (a finite index set $J$, degrees $d_0 : J \to \mathbb Z$ and a degreewise surjective homomorphism from the product of the free graded modules $\mathrm{FD}(d_0\,k)$ onto $D$), and a homomorphism of graded modules $h : D \to M$ such that the underlying linear map of $h$ is injective and, for every $e\in\mathbb Z$, every $f$ in the degree-$e$ part of $M$ and every $l\in\mathrm{Fin}(r+1)$, there are $N\in\mathbb N$ and $f'$ in the degree-$(e+N)$ part of $D$ with $h(f') = x_l^N f$.
--
--   This is the finiteness statement for the graded module of frames sections of a family of coherent sheaves on a closed subscheme of $\mathbb P^r_A$ with commuting generating transition operators: the module is sandwiched between a finitely generated graded module over $A[y_1,\dots ,y_s][x_0,\dots ,x_r]$ and itself, injectively and with agreement after saturation at each $x_l$, so that the two have the same localisations at the $x_l$ and hence the same Čech complexes in every twist. It is used for uniform Serre vanishing for the graded pieces of an adic system, in [`AlgebraicGeometry.OModulePresheaf.exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_isFG_hom_injective_saturated_familyFramesGradedModule
    {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsClosedImmersion ι]
    {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (G : ℕ → OModulePresheaf q) (hc : ∀ k, (G k).IsCoherent) (hq : ∀ k, (G k).IsQuasicoherent)
    {s : ℕ} (θ : Fin s → ∀ k : ℕ, OModulePresheaf.AffHom (G k) (G (k + 1))) (hθ : OModulePresheaf.YComm G θ)
    (hgen : ∀ (k : ℕ) (U : P.affineOpens), (⨆ m : Fin s, LinearMap.range ((θ m k).app U)) = ⊤) :
    ∃ (D : ProjSpaceCech.GradedModule (MvPolynomial (Fin s) A) r) (_ : ProjSpaceCech.GradedModule.IsFG D)
      (h : ProjSpaceCech.GradedModule.Hom D (OModulePresheaf.familyFramesGradedModule ι G θ hθ)),
      Function.Injective h.toLinearMap ∧
      ∀ (e : ℤ) (f : (OModulePresheaf.familyFramesGradedModule ι G θ hθ).M),
        f ∈ (OModulePresheaf.familyFramesGradedModule ι G θ hθ).grade e → ∀ l : Fin (r + 1),
          ∃ (N : ℕ) (f' : D.M), f' ∈ D.grade (e + N) ∧
            h.toLinearMap f' = ((OModulePresheaf.familyFramesGradedModule ι G θ hθ).xMul l ^ N) f := by sorry
