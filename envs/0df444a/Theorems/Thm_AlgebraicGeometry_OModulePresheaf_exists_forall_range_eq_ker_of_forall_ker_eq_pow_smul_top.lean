-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/0a115306-590c-5ae1-acda-a5a1eab054ca
-- title:
--   Kernels of I-adic systems of coherent module presheaves
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal, and $q : P \to \operatorname{Spec} A$ a morphism of schemes locally of finite type. Here an `OModulePresheaf q` is a family of $A$-modules $\mathcal F(U)$ indexed by the opens of $P$, each also a $\Gamma(P,U)$-module compatibly with the $A$-action, together with $A$-linear restriction maps that are semilinear over the restriction maps of $\mathcal O_P$ and satisfy the usual identity and composition laws; `IsCoherent` asserts that $\mathcal F(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and `IsQuasicoherent` that for every affine open $U$ and $f \in \Gamma(P,U)$ each section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$; an `AffHom` is a family of $\Gamma(P,U)$-semilinear $A$-linear maps on affine opens commuting with restriction. Given sequences $G, F : \mathbb N \to$ `OModulePresheaf q`, all members coherent and quasi-coherent, transition morphisms $\gamma_k : G(k+1) \to G(k)$ and $\varphi_k : F(k+1) \to F(k)$ which on every affine open $U$ are surjective with kernel $I^{k+1} \cdot G(k+1)(U)$, respectively $I^{k+1} \cdot F(k+1)(U)$, and morphisms $\theta_k : G(k) \to F(k)$ surjective on every affine open with $\varphi_k \circ \theta_{k+1} = \theta_k \circ \gamma_k$ on every affine open, the conclusion asserts the existence of a sequence $K : \mathbb N \to$ `OModulePresheaf q` with morphisms $\kappa_k : K(k+1) \to K(k)$ and $j_k : K(k) \to G(k)$ such that each $K(k)$ is coherent and quasi-coherent, each $\kappa_k$ is surjective on every affine open with kernel $I^{k+1} \cdot K(k+1)(U)$, the squares $\gamma_k \circ j_{k+1} = j_k \circ \kappa_k$ commute on every affine open, and on every affine open the range of $j_k$ equals the kernel of $\theta_k$.
--
--   This is the existence of kernels for coherent modules on the formal completion of $P$ along $I$, presented concretely as $I$-adic systems of coherent module data on affine opens: the termwise kernels of a surjection of adic systems need not form an adic system, and the statement produces a corrected system agreeing termwise with those kernels. It is used in the construction of $I$-adic systems of coherent sheaves from a closed immersion together with adic completeness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType q]
    (G F : ℕ → OModulePresheaf q)
    (hGc : ∀ k, (G k).IsCoherent) (hGq : ∀ k, (G k).IsQuasicoherent)
    (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (γ : ∀ k, OModulePresheaf.AffHom (G (k + 1)) (G k))
    (hγs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((γ k).app U))
    (hγk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((γ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((G (k + 1)).obj U.1)))
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (θ : ∀ k, OModulePresheaf.AffHom (G k) (F k))
    (hθs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θ k).app U))
    (hθc : ∀ (k : ℕ) (U : P.affineOpens),
      (φ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U ∘ₗ (γ k).app U) :
    ∃ (K : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (K (k + 1)) (K k))
      (j : ∀ k, OModulePresheaf.AffHom (K k) (G k)),
      (∀ k, (K k).IsCoherent) ∧ (∀ k, (K k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((K (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((j k).app U) = LinearMap.ker ((θ k).app U)) := by sorry
