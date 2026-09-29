-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le
-- name    : AlgebraicGeometry.OModulePresheaf.exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/14b42179-3812-5c3c-9aa8-82a40729c49b
-- title:
--   Adic envelope of an Artin–Rees-stable subsystem
-- statement:
--   Let $A$ be a commutative ring, $I\subseteq A$ an ideal, $P$ a scheme and $q\colon P\to\operatorname{Spec}A$ a morphism; by a sheaf is meant here an object of `OModulePresheaf q`, i.e. an assignment to each open $U\subseteq P$ of an $A$-module which is also a $\Gamma(P,U)$-module compatibly over $A$, together with $A$-linear restriction maps that are semilinear for restriction of sections and satisfy the identity and composition laws; a morphism (`AffHom`) is a family of $\Gamma(P,U)$-linear maps indexed by the affine opens $U$ of $P$, commuting with restrictions along inclusions of affine opens. Given a family $F_n$ of such sheaves with morphisms $\varphi_n\colon F_{n+1}\to F_n$ that are surjective on every affine open and satisfy $\ker(\varphi_n)_U=I^{n+1}\cdot F_{n+1}(U)$ (the submodule generated over $A$ by $I^{n+1}$ applied to all of $F_{n+1}(U)$), and given sheaves $L_n$ that are coherent (each $L_n(U)$ is a finite $\Gamma(P,U)$-module for $U$ affine) and quasi-coherent (for $U$ affine and $f\in\Gamma(P,U)$, every section over the basic open $P_f\cap U$ becomes, after multiplication by a power of $f$, the restriction of a section over $U$, and a section over $U$ restricting to $0$ is annihilated by a power of $f$), with morphisms $\iota_n\colon L_n\to F_n$ injective on affine opens and $\lambda_n\colon L_{n+1}\to L_n$ surjective on affine opens satisfying $(\iota_n)_U\circ(\lambda_n)_U=(\varphi_n)_U\circ(\iota_{n+1})_U$, and assuming the Artin–Rees estimate that for each affine open $U$ there is $c$ with $I^n\cdot F_n(U)\cap\operatorname{im}(\iota_n)_U\subseteq I^k\cdot\operatorname{im}(\iota_n)_U$ whenever $k+c\le n$: then there exist sheaves $K_k$ with morphisms $\kappa_k\colon K_{k+1}\to K_k$ and $j_k\colon K_k\to F_k$ such that every $K_k$ is coherent and quasi-coherent, each $\kappa_k$ is surjective on affine opens with $\ker(\kappa_k)_U=I^{k+1}\cdot K_{k+1}(U)$, the squares commute in the form $(\varphi_k)_U\circ(j_{k+1})_U=(j_k)_U\circ(\kappa_k)_U$, the images satisfy $\operatorname{im}(j_k)_U=\operatorname{im}(\iota_k)_U$ on every affine open, and for each affine open $U$ there is $c$ with $\ker(j_n)_U\subseteq I^{k+1}\cdot K_n(U)$ whenever $k+c\le n$.
--
--   This is the passage from an Artin–Rees-stable coherent subsystem $(L_n)$ of an $I$-adic system $(F_n)$ to an honest $I$-adic system $(K_k)$ having the same images in $(F_n)$, with kernels that are Artin–Rees-small; concretely $K_k$ is the reduction modulo $I^{k+1}$ of the inverse limit of the $L_n$. It is used in the construction of kernels and cokernels of morphisms of adic systems of coherent sheaves, through [`AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf q)
    (φ : ∀ n, OModulePresheaf.AffHom (F (n + 1)) (F n))
    (hφs : ∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((φ n).app U))
    (hφk : ∀ (n : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ n).app U) = I ^ (n + 1) • (⊤ : Submodule A ((F (n + 1)).obj U.1)))
    (L : ℕ → OModulePresheaf q) (hLc : ∀ n, (L n).IsCoherent) (hLq : ∀ n, (L n).IsQuasicoherent)
    (ι : ∀ n, OModulePresheaf.AffHom (L n) (F n))
    (hιi : ∀ (n : ℕ) (U : P.affineOpens), Function.Injective ((ι n).app U))
    (lam : ∀ n, OModulePresheaf.AffHom (L (n + 1)) (L n))
    (hls : ∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((lam n).app U))
    (hlc : ∀ (n : ℕ) (U : P.affineOpens), (ι n).app U ∘ₗ (lam n).app U = (φ n).app U ∘ₗ (ι (n + 1)).app U)
    (hAR : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      I ^ n • (⊤ : Submodule A ((F n).obj U.1)) ⊓ LinearMap.range ((ι n).app U) ≤ I ^ k • LinearMap.range ((ι n).app U)) :
    ∃ (Ks : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (Ks (k + 1)) (Ks k))
      (j : ∀ k, OModulePresheaf.AffHom (Ks k) (F k)),
      (∀ k, (Ks k).IsCoherent) ∧ (∀ k, (Ks k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((j k).app U) = LinearMap.range ((ι k).app U)) ∧
      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
        LinearMap.ker ((j n).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ks n).obj U.1))) := by sorry
