-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/64a6ff90-3c49-5694-8895-5a62529e548c
-- title:
--   Annihilation of a K-system by J₂^{ t} via Artin–Rees bookkeeping
-- statement:
--   Let $A$ be a commutative ring, $I\subseteq A$ an ideal, and $q:P\to\operatorname{Spec} A$ a morphism of schemes. Let $S,K:\mathbb N\to$ `OModulePresheaf q` be two systems of module data on $P$ (each assigning to every open $U$ an $A$-module and a $\Gamma(P,U)$-module compatibly, with restriction maps), equipped with transition maps $\varphi_k$ from $S(k+1)$ to $S(k)$ and $\kappa_k$ from $K(k+1)$ to $K(k)$ (families of $A$-linear, $\Gamma(P,U)$-semilinear maps on affine opens commuting with restriction), such that on every affine open $U$ the maps $\varphi_k(U)$ and $\kappa_k(U)$ are surjective with kernels $I^{k+1}\,S_{k+1}(U)$ and $I^{k+1}\,K_{k+1}(U)$ respectively. Let $j_k:K_k\to S_k$ be maps of the same kind satisfying $\varphi_k(U)\circ j_{k+1}(U)=j_k(U)\circ\kappa_k(U)$. Let $\mathcal J,\mathcal J_1,\mathcal J_2$ be ideal sheaf data on $P$ and $s,t\in\mathbb N$, and assume: the image of $j_k(U)$ is $\mathcal J_1(U)\cdot S_k(U)$ for all $k$ and all affine $U$; for each affine $U$ there is $c$ with $\ker j_{k+c}(U)\subseteq I^{k+1}K_{k+c}(U)$ for all $k$; $\mathcal J_2(U)^t\mathcal J_1(U)\subseteq\mathcal J(U)^s$; and every $a\in\mathcal J(U)^s$ annihilates $S_k(U)$. Then every $a\in\mathcal J_2(U)^t$ annihilates $K_k(U)$, for all $k$ and all affine opens $U$.
--
--   This is the Artin–Rees style bookkeeping step which transports an annihilator from one adic system of module data to another along a map whose image is an ideal multiple. It is used in the dévissage leading to [`AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete), the existence statement for proper morphisms over an adically complete base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (S : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (S (k + 1)) (S k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((S (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (K (k + 1)) (K k))
    (hκs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U))
    (hκk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((K (k + 1)).obj U.1)))
    (j : ∀ k, OModulePresheaf.AffHom (K k) (S k))
    (hjc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U)
    (𝓙 𝓙₁ 𝓙₂ : P.IdealSheafData) (s t : ℕ)
    (hjr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((j k).app U) = OModulePresheaf.idealPowSub q 𝓙₁ (S k) 1 U.1)
    (hji : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((j (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((K (k + c)).obj U.1)))
    (hle : ∀ U : P.affineOpens, 𝓙₂.ideal U ^ t * 𝓙₁.ideal U ≤ 𝓙.ideal U ^ s)
    (hS : ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ 𝓙.ideal U ^ s, ∀ x : (S k).obj U.1, a • x = 0) :
    ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ 𝓙₂.ideal U ^ t, ∀ y : (K k).obj U.1, a • y = 0 := by sorry
