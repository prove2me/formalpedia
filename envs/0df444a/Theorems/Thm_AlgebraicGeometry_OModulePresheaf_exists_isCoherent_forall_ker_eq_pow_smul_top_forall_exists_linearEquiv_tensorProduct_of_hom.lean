-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/a6f17248-1312-5592-93ed-4a87faf96112
-- title:
--   Inverse image of an I-adic system of coherent modules
-- statement:
--   Let $A$ be a commutative ring, $I \subseteq A$ an ideal, and let $q \colon P \to \operatorname{Spec} A$ and $p \colon V' \to P$ be morphisms of schemes. Let $F$ assign to each $k \in \mathbb{N}$ a module presheaf over $q$, that is, a family of modules $(F k).obj\,U$ indexed by the opens $U$ of $P$, each carrying compatible $A$- and $\Gamma(P,U)$-module structures (the $A$-algebra structure on sections coming from $q$), together with $A$-linear restriction maps that are semilinear over restriction of sections and functorial. Assume each $F k$ is coherent (i.e. $(F k).obj\,U$ is a finite $\Gamma(P,U)$-module for every affine open $U$) and quasi-coherent (i.e. for every affine open $U$ and $f \in \Gamma(P,U)$, every section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, a restriction from $U$, and every section over $U$ restricting to $0$ on $D(f)$ is killed by some power of $f$). Assume given transition maps $\varphi_k \colon F(k+1) \to F k$, each consisting of $A$-linear maps on affine opens that are $\Gamma(P,U)$-linear and commute with restriction, such that on every affine open $U$ of $P$ the map $(\varphi_k).app\,U$ is surjective with kernel $I^{k+1} \cdot (F(k+1)).obj\,U$ (as $A$-submodules). The conclusion asserts the existence of module presheaves $F'k$ over $p \circ q$, transition maps $\varphi'_k \colon F'(k+1) \to F'k$ of the same kind, and $A$-linear maps $\eta_{k,U,V} \colon (F k).obj\,U \to (F'k).obj\,V$ for all affine opens $U$ of $P$, $V$ of $V'$ with $V \subseteq p^{-1}(U)$, such that: every $F'k$ is coherent and quasi-coherent; $(\varphi'_k).app\,V$ is surjective with kernel $I^{k+1} \cdot (F'(k+1)).obj\,V$ on every affine open $V$ of $V'$; each $\eta_{k,U,V}$ is semilinear along $p^\sharp \colon \Gamma(P,U) \to \Gamma(V',V)$; the $\eta$ are compatible with shrinking $V$ and with shrinking $U$ (restricting first in $F k$), and satisfy $(\varphi'_k).app\,V \circ \eta_{k+1,U,V} = \eta_{k,U,V} \circ (\varphi_k).app\,U$; for each such $U, V$, regarding $\Gamma(V',V)$ as a $\Gamma(P,U)$-algebra via $p^\sharp$, there is a $\Gamma(V',V)$-linear isomorphism $\beta \colon \Gamma(V',V) \otimes_{\Gamma(P,U)} (F k).obj\,U \to (F'k).obj\,V$ with $\beta(1 \otimes x) = \eta_{k,U,V}(x)$; and finally, if $W'$ is an affine open of $V'$ with $W' = p^{-1}(W)$ for an affine open $W$ of $P$ and the restriction $p|_W \colon p^{-1}(W) \to W$ is an isomorphism, then $\eta_{k,W,W'}$ is bijective.
--
--   This is the statement that the inverse image along $p$ of an $I$-adic system of coherent modules on $P$ is again such a system on $V'$, with the unit maps realising $(p^*F_k)(V)$ as $\Gamma(V',V) \otimes_{\Gamma(P,U)} F_k(U)$ on affine opens. It is used in the reduction, via Chow's lemma, of the finiteness/existence theorem for proper morphisms and $I$-adically complete base rings to the projective case, being cited by [`AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom
    {A : Type u} [CommRing A] (I : Ideal A)
    {P V' : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P)
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (F' : ℕ → OModulePresheaf (p ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
      (η : ∀ (k : ℕ) (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → ((F k).obj U.1 →ₗ[A] (F' k).obj V.1)),
      (∀ k, (F' k).IsCoherent) ∧ (∀ k, (F' k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (V : V'.affineOpens), Function.Surjective ((φ' k).app V)) ∧
      (∀ (k : ℕ) (V : V'.affineOpens),
        LinearMap.ker ((φ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A ((F' (k + 1)).obj V.1))) ∧

      (∀ (k : ℕ) (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : (F k).obj U.1),
        η k U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η k U V h x) ∧

      (∀ (k : ℕ) (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
        (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U.1), (F' k).res hV (η k U V₂ h₂ x) = η k U V₁ h₁ x) ∧

      (∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
        (hU : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1), η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU x)) ∧

      (∀ (k : ℕ) (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (x : (F (k + 1)).obj U.1),
        (φ' k).app V (η (k + 1) U V h x) = η k U V h ((φ k).app U x)) ∧

      (∀ (k : ℕ) (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
        letI := (p.appLE U.1 V.1 h).hom.toAlgebra
        ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] (F k).obj U.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
          ∀ x : (F k).obj U.1, β (1 ⊗ₜ x) = η k U V h x) ∧

      (∀ (k : ℕ) (W : P.affineOpens) (W' : V'.affineOpens) (hW : W'.1 = p ⁻¹ᵁ W.1),
        IsIso (p ∣_ W.1) → Function.Bijective (η k W W' hW.le)) := by sorry
