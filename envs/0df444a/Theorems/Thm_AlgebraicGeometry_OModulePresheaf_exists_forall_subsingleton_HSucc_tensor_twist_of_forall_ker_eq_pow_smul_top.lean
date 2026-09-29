-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/3fc9565f-cec1-5c03-bf62-16540271f43a
-- title:
--   Uniform Serre vanishing for twisted kernels of an I-adic system
-- statement:
--   Let $A$ be a Noetherian commutative ring and $I \subseteq A$ an ideal, let $r \in \mathbb{N}$, and let $\iota : P \to \operatorname{Proj}$ of the graded algebra of homogeneous polynomials in $\mathrm{Fin}(r+1)$ variables over $A$ be a closed immersion, with $q : P \to \operatorname{Spec} A$ such that $\iota$ followed by the structure morphism $\pi$ of $\mathbb{P}^r_A$ equals $q$. Let $F_k$, $k \in \mathbb{N}$, be module data over $q$ (for each open $U$ an $A$-module and $\Gamma(P,U)$-module $F_k(U)$ with compatible restrictions), each coherent, i.e. $F_k(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and each quasi-coherent in the sense that on basic opens of affine opens sections extend after multiplication by a power of the function and sections dying on a basic open are killed by such a power. Let $\varphi_k$ be morphisms $F_{k+1} \to F_k$ given on affine opens by $\Gamma$-compatible $A$-linear maps commuting with restriction, such that on every affine open $U$ the map is surjective with kernel $I^{k+1} \cdot F_{k+1}(U)$. Let further $K_k$ be coherent quasi-coherent module data over $q$ with morphisms $j_k : K_k \to F_{k+1}$ which on every affine open are injective with image exactly $\ker \varphi_k$. Then there is $d_0 \in \mathbb{N}$ such that for all $d \geq d_0$ and all $k, i \in \mathbb{N}$ the group $\ker(\mathrm{d}^{i+1})/\operatorname{im}(\mathrm{d}^{i})$ of the Čech complex of the twist $K_k \otimes \iota^{*}\mathcal{O}(d)$ — the open-by-open tensor product over $\Gamma(P,U)$ of $K_k$ with the twist datum in the standard frames — relative to the ordered affine cover of $P$ by the $\iota$-preimages of the standard charts $D_+(x_j)$ is trivial. In particular the bound $d_0$ is uniform in both the adic level $k$ and the cohomological degree.
--
--   This is the uniform form of Serre's vanishing theorem needed for an $I$-adic system on a closed subscheme of projective space: a single twist suffices to kill all higher Čech cohomology of all the kernel data $K_k$ simultaneously. It feeds the companion statement that the induced maps on $H^0$ of the twisted quotients are surjective for large twists, the step by which cohomology of the system is controlled level by level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (hKc : ∀ k, (K k).IsCoherent) (hKq : ∀ k, (K k).IsQuasicoherent)
    (j : ∀ k, OModulePresheaf.AffHom (K k) (F (k + 1)))
    (hji : ∀ (k : ℕ) (U : P.affineOpens), Function.Injective ((j k).app U))
    (hjr : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((j k).app U) = LinearMap.ker ((φ k).app U)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ (k i : ℕ),
      Subsingleton (((K k).tensor (ProjSpace.twist q ι d)).HSucc (ProjSpace.stdCoverPullback ι) i) := by sorry
