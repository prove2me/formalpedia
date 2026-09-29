-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/f3941efe-4627-54d3-a267-c58014158020
-- title:
--   Finite generation up to x-saturation of family frames
-- statement:
--   Let $A$ be a commutative ring, $r\in\mathbb N$, and let $\iota\colon P\to\operatorname{Proj}$ of the homogeneous subalgebra of $A[x_0,\dots ,x_r]$ be a finite morphism whose composite with the structure map $\mathrm{ProjSpace.\pi}$ equals $q\colon P\to\operatorname{Spec}A$. Let $G\colon\mathbb N\to$ `OModulePresheaf q` be a family of presheaves of modules over $q$ (each $U$ gets an $A$-module and $\Gamma(P,U)$-module with compatible restriction maps), with every $G_k$ coherent (i.e. $G_k(U)$ finite over $\Gamma(P,U)$ for affine $U$) and quasicoherent (on basic opens $D(f)\subseteq U$ affine: every section is $f^n$ times a restriction, and a section restricting to $0$ is killed by some $f^n$). Let $\theta_m\colon G_k\to G_{k+1}$, $m\in\mathrm{Fin}\,s$, be maps of affine-open sections, pairwise commuting (`YComm`), such that for all $k$ and affine $U$ the ranges of the $(\theta_m)_U$ span $G_{k+1}(U)$. Write $M$ for `familyFramesGradedModule ι G θ hθ`: the graded module over $A[y_1,\dots ,y_s]$ with $r+1$ multiplications $x_l$, whose elements are families $f(e,k,j)\in G_k(\iota^{-1}D_+(x_j))$, degree-$e$ part consisting of those concentrated in degree $e\ge 0$, frames-compatible in each $k$, with finitely many nonzero $k$, the $x_l$ acting by the frame units and the $y_m$ through $\theta$. Then there exist a graded module $D$ over $A[y_1,\dots ,y_s]$ with $r+1$ multiplications that is finitely generated (admits a presentation by a finite product of shifted free graded modules, surjective in each degree), and a graded homomorphism $h\colon D\to M$ (grade-preserving and commuting with all $x_l$) with $h$ injective, such that for every $e\in\mathbb Z$, every $f\in M_e$ and every $l\in\mathrm{Fin}(r+1)$ there are $N\in\mathbb N$ and $f'\in D_{e+N}$ with $h(f')=x_l^N f$.
--
--   This is the finite-morphism version of the statement that the graded module of frames of a commuting family of coherent module data on $P$ is finitely generated up to saturation by the homogeneous coordinates, the graded-module substitute for Serre's finiteness results on $\operatorname{Proj}$. It feeds the vanishing statement [`AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite
    {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsFinite ι]
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
