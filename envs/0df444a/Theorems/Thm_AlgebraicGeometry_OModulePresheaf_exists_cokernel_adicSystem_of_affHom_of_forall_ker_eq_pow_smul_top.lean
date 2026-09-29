-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/f5ecf09b-8438-5d9b-b041-4f0add92bbe2
-- title:
--   Levelwise cokernels of a map into an I-adic system
-- statement:
--   Let $A$ be a commutative ring, $I\subseteq A$ an ideal, $P$ a scheme and $q:P\to\operatorname{Spec}A$ a morphism. Sheaf data are given by `OModulePresheaf q`: for each open $U$ of $P$ a module carrying compatible $A$- and $\Gamma(P,U)$-module structures (the $A$-structure coming from $q$), together with $A$-linear restriction maps along inclusions that are semilinear over the restriction of sections and satisfy the reflexivity and composition identities; a morphism is an `AffHom`, i.e. a family of $A$-linear maps on the sections over each affine open, semilinear for the $\Gamma$-action and commuting with restriction between affine opens. Assume given: a family $F_k$ ($k\in\mathbb N$) of such data, each quasi-coherent in the sense that for every affine open $U$ and $f\in\Gamma(P,U)$ every section over the basic open $D(f)$ becomes the restriction of a section over $U$ after multiplication by some power of $f$, and every section over $U$ restricting to $0$ on $D(f)$ is annihilated by a power of $f$; morphisms $\varphi_k:F_{k+1}\to F_k$ surjective on each affine open; a family $P_k$ that is coherent (sections over each affine open $U$ form a finite $\Gamma(P,U)$-module) and quasi-coherent, with morphisms $\pi_k:P_{k+1}\to P_k$ surjective on every affine open $U$ and with $\ker\pi_k(U)=I^{k+1}\cdot P_{k+1}(U)$ as $A$-submodules; and morphisms $u_k:F_k\to P_k$ with $\pi_k\circ u_{k+1}=u_k\circ\varphi_k$ on every affine open. Then there exist data $C_k$ with morphisms $\gamma_k:C_{k+1}\to C_k$ and $\theta_k:P_k\to C_k$ such that every $C_k$ is coherent and quasi-coherent, each $\gamma_k$ is surjective on affine opens with $\ker\gamma_k(U)=I^{k+1}\cdot C_{k+1}(U)$, $\gamma_k\circ\theta_{k+1}=\theta_k\circ\pi_k$ on affine opens, and each $\theta_k$ is surjective on affine opens with $\ker\theta_k(U)=\operatorname{im}u_k(U)$.
--
--   This is the statement that the levelwise cokernels of a morphism from a quasi-coherent system into an $I$-adic system of coherent sheaf data again form an $I$-adic system of coherent sheaf data, with the cokernel maps $\theta_k$ fitting into exact sequences $F_k(U)\to P_k(U)\to C_k(U)\to 0$ over affine opens. It feeds into the combined kernel–cokernel statement [`AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top), part of the coherent-sheaf machinery over an adically complete base used in the deformation-theoretic input to modularity lifting; the individual cokernel at each level is produced by [`AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_surjective_ker_eq_range`](thm.html#AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_surjective_ker_eq_range).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf q) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U) :
    ∃ (Cs : ℕ → OModulePresheaf q) (γ : ∀ k, OModulePresheaf.AffHom (Cs (k + 1)) (Cs k))
      (θ : ∀ k, OModulePresheaf.AffHom (Ps k) (Cs k)),
      (∀ k, (Cs k).IsCoherent) ∧ (∀ k, (Cs k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((γ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((γ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Cs (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U ∘ₗ (π k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.ker ((θ k).app U) = LinearMap.range ((u k).app U)) := by sorry
