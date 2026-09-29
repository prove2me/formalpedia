-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc
-- name    : AlgebraicGeometry.Scheme.Modules.exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/5922a8aa-425b-5514-b780-d0a98a8b2fe1
-- title:
--   Lifting sections along a small thickening of a local base
-- statement:
--   Let $R$ be a commutative local ring, $R_0$ a commutative ring and $k$ a field, all in one universe. Let $\pi : R \to R_0$ be a surjective ring homomorphism whose kernel satisfies $\ker\pi \cdot \mathfrak m = 0$, where $\mathfrak m$ is the maximal ideal of $R$, and let $s : R \to k$ be a surjective ring homomorphism with $\ker s = \mathfrak m$. Let $f : X \to \operatorname{Spec} R$ be proper and flat, let $f_0 : X_0 \to \operatorname{Spec} R_0$ and $g : X_0 \to X$ exhibit $X_0$ as the pullback of $f$ along $\operatorname{Spec}\pi$, and let $f_k : X_k \to \operatorname{Spec} k$ and $g_k : X_k \to X$ exhibit $X_k$ as the pullback of $f$ along $\operatorname{Spec} s$. Let $\mathcal M$ be a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the restriction of $\mathcal M$ to $U$ is isomorphic to the unit sheaf of modules on $U$. Assume that for every ordered affine cover $\mathcal U$ of $X_k$ (a finite, linearly ordered family of affine opens with supremum $\top$) the group $\mathrm{HSucc}\,\mathcal U\,0$ of the $\mathcal O$-module presheaf of sections of $g_k^{*}\mathcal M$ over $f_k$ — that is, $\ker d^{1}$ modulo the image of $d^{0}$, the first Čech cohomology of $\mathcal U$ — is a subsingleton. Then for every section $s_0$ of $g^{*}\mathcal M$ over $g^{-1}(\top)$ there is a global section $\sigma$ of $\mathcal M$ over $\top$ whose canonical pullback, the adjunction unit applied to $\sigma$, equals $s_0$.
--
--   This is the surjectivity of $H^0(X,\mathcal M) \to H^0(X_0, g^{*}\mathcal M)$ for a small extension $R \to R_0$ of a local base, the section-lifting step supplied by cohomology and base change together with the vanishing of $H^1$ on the closed fibre. It is used in the construction of towers of finite maps for fake elliptic curves, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFinite_proj_tower_of_finiteBySections`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFinite_proj_tower_of_finiteBySections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc
    {R R₀ k : Type u} [CommRing R] [IsLocalRing R] [CommRing R₀] [Field k]
    (π : R →+* R₀) (hπ : Function.Surjective π) (hsmall : RingHom.ker π * IsLocalRing.maximalIdeal R = ⊥)
    (s : R →+* k) (hs : Function.Surjective s) (hsk : RingHom.ker s = IsLocalRing.maximalIdeal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of R₀)) (g : X₀ ⟶ X)
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (.of k)) (gk : Xk ⟶ X)
    (hgk : IsPullback gk fk f (Spec.map (CommRingCat.ofHom s)))
    (𝓜 : X.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (hvan : ∀ 𝒰 : Xk.OrderedAffineCover,
      Subsingleton ((OModulePresheaf.ofModules fk ((Scheme.Modules.pullback gk).obj 𝓜)).HSucc 𝒰 0))
    (s₀ : Γ((Scheme.Modules.pullback g).obj 𝓜, g ⁻¹ᵁ ⊤)) :
    ∃ σ : Γ(𝓜, ⊤), Scheme.Modules.pullbackLocalSection g σ = s₀ := by sorry
