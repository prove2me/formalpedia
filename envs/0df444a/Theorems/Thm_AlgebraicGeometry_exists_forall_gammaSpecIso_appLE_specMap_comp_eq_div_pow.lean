-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_forall_gammaSpecIso_appLE_specMap_comp_eq_div_pow
-- name    : AlgebraicGeometry.exists_forall_gammaSpecIso_appLE_specMap_comp_eq_div_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/ef379dae-fbd2-5620-bf0c-cd4d19d067e3
-- title:
--   Values of a regular function at K-points are rational in the point
-- statement:
--   Let $K$ be a field and $S$ a commutative $K$-algebra (both in a fixed universe), let $Y$ be a scheme, $P : \operatorname{Spec} S \to Y$ a morphism of schemes, $V$ an open subscheme of $Y$, and $\varphi \in \Gamma(Y, V)$ a section over $V$. Let $\sigma_1 : S \to K$ be a $K$-algebra homomorphism whose associated $K$-point, namely $\operatorname{Spec}$ of $\sigma_1$ followed by $P$, has the whole of $\operatorname{Spec} K$ contained in the preimage of $V$. The assertion is that there exist $s_0, a \in S$ and $k \in \mathbb{N}$ with $\sigma_1(s_0) \neq 0$ such that for every $K$-algebra homomorphism $\sigma : S \to K$ with $\sigma(s_0) \neq 0$ the composite $\operatorname{Spec}(\sigma)$ followed by $P$ again pulls $V$ back to all of $\operatorname{Spec} K$, and, for the resulting restricted pullback map $\Gamma(Y,V) \to \Gamma(\operatorname{Spec} K, \top)$ applied to $\varphi$ and then read in $K$ through the canonical isomorphism $\Gamma(\operatorname{Spec} K, \top) \cong K$, one has the identity $\sigma(a)/\sigma(s_0)^k$. Thus a single pair $(a, s_0)$ and a single exponent $k$ work uniformly for all $K$-points in the basic open locus $\sigma(s_0) \neq 0$.
--
--   This is the scheme-theoretic statement that the value of a regular function along a family of $K$-rational points of an affine test scheme is a fixed rational function of the point, obtained by shrinking to a basic open on which the section becomes a fraction. It is used in the construction of fake elliptic curves with full level structure, where it supplies uniform algebraic formulae for chart coordinates of a uniformising family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_forall_gammaSpecIso_appLE_specMap_comp_eq_div_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_forall_gammaSpecIso_appLE_specMap_comp_eq_div_pow
    {K : Type u} [Field K] {S : Type u} [CommRing S] [Algebra K S]
    {Y : Scheme.{u}} (P : Spec (CommRingCat.of S) ⟶ Y) (V : Y.Opens) (φ : Γ(Y, V))
    (σ₁ : S →ₐ[K] K) (h₁ : ⊤ ≤ (Spec.map (CommRingCat.ofHom σ₁.toRingHom) ≫ P) ⁻¹ᵁ V) :
    ∃ (s₀ a : S) (k : ℕ), σ₁ s₀ ≠ 0 ∧
      ∀ σ : S →ₐ[K] K, σ s₀ ≠ 0 →
        ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ P) ⁻¹ᵁ V,
          (Scheme.ΓSpecIso (CommRingCat.of K)).hom
              (((Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ P).appLE V ⊤ h) φ) = σ a / σ s₀ ^ k := by sorry
