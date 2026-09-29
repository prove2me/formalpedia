-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/6838dcf5-f1be-517a-9e88-807a0e6177a9
-- title:
--   Kernel and cokernel systems of a morphism of I-adic systems
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I\subseteq A$ an ideal, $P$ a scheme and $q\colon P\to\operatorname{Spec}A$ a morphism locally of finite type. Sheaf data are taken in the form `OModulePresheaf q`: an assignment of an $A$-module and $\Gamma(P,U)$-module to each open $U$, with compatible scalar towers and $A$-linear restriction maps, semilinear for restriction of sections and functorial; `IsCoherent` means each $F(U)$ with $U$ affine open is a finite $\Gamma(P,U)$-module, `IsQuasicoherent` means that for each affine open $U$ and $f\in\Gamma(P,U)$ every section over $P_f$ becomes a restriction after multiplication by a power of $f$ and every section over $U$ restricting to $0$ on $P_f$ is annihilated by a power of $f$; an `AffHom` is a family of $A$-linear maps on affine opens, compatible with multiplication by sections and with restrictions. Given families $F,\,Ps\colon\mathbb N\to$ `OModulePresheaf q`, all coherent and quasi-coherent, with transition `AffHom`s $\varphi_k\colon F(k+1)\to F(k)$ and $\pi_k\colon Ps(k+1)\to Ps(k)$ that are surjective on every affine open $U$ with kernels exactly $I^{k+1}\cdot F(k+1)(U)$, resp. $I^{k+1}\cdot Ps(k+1)(U)$, and `AffHom`s $u_k\colon F(k)\to Ps(k)$ with $\pi_k\circ u_{k+1}=u_k\circ\varphi_k$ on every affine open, the conclusion asserts the existence of families $Ks$, $Cs$ with transition `AffHom`s $\kappa_k\colon Ks(k+1)\to Ks(k)$, $\gamma_k\colon Cs(k+1)\to Cs(k)$ and `AffHom`s $j_k\colon Ks(k)\to F(k)$, $\theta_k\colon Ps(k)\to Cs(k)$ such that: all $Ks(k)$ and $Cs(k)$ are coherent and quasi-coherent; $\kappa_k$ and $\gamma_k$ are surjective on every affine open with kernels $I^{k+1}\cdot Ks(k+1)(U)$, resp. $I^{k+1}\cdot Cs(k+1)(U)$; $\varphi_k\circ j_{k+1}=j_k\circ\kappa_k$ and $\gamma_k\circ\theta_{k+1}=\theta_k\circ\pi_k$ on affine opens; $u_k\circ j_k=0$; for every affine open $U$ there is $c\in\mathbb N$ with, for all $k$, $\ker u_{k+c}(U)\subseteq \operatorname{im}j_{k+c}(U)+I^{k+1}\cdot F(k+c)(U)$ and $\ker j_{k+c}(U)\subseteq I^{k+1}\cdot Ks(k+c)(U)$; if moreover every $u_k$ is surjective on every affine open, then $\operatorname{im}j_k(U)=\ker u_k(U)$ for all $k$ and $U$; and each $\theta_k$ is surjective on every affine open with $\ker\theta_k(U)=\operatorname{im}u_k(U)$.
--
--   This is the statement that the category of $I$-adic inverse systems of coherent modules on a scheme locally of finite type over a Noetherian base admits kernels and cokernels: cokernels are computed levelwise, while the kernel system is only an Artin–Rees approximation of the levelwise kernels, becoming exact when the given morphism is levelwise surjective. It is used in the construction of coherent adic systems with prescribed transition kernels on proper schemes over adically complete bases, and in the comparison of Čech pushforwards of such systems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U) :
    ∃ (Ks : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (Ks (k + 1)) (Ks k))
      (j : ∀ k, OModulePresheaf.AffHom (Ks k) (F k))
      (Cs : ℕ → OModulePresheaf q) (γ : ∀ k, OModulePresheaf.AffHom (Cs (k + 1)) (Cs k))
      (θ : ∀ k, OModulePresheaf.AffHom (Ps k) (Cs k)),

      (∀ k, (Ks k).IsCoherent) ∧ (∀ k, (Ks k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + 1)).obj U.1))) ∧

      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (u k).app U ∘ₗ (j k).app U = 0) ∧

      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
        LinearMap.ker ((u (k + c)).app U)
          ≤ LinearMap.range ((j (k + c)).app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj U.1)) ∧
        LinearMap.ker ((j (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + c)).obj U.1))) ∧

      ((∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((u k).app U)) →
        ∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((j k).app U) = LinearMap.ker ((u k).app U)) ∧

      (∀ k, (Cs k).IsCoherent) ∧ (∀ k, (Cs k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((γ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((γ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Cs (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U ∘ₗ (π k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.ker ((θ k).app U) = LinearMap.range ((u k).app U)) := by sorry
