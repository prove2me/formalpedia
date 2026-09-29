-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
-- name    : AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/e88c5cdd-8160-5a2b-8b47-c23eb953a688
-- title:
--   Semilinear family η induces an affine morphism into the Čech pushforward
-- statement:
--   Let $A$ be a commutative ring, let $q : P \to \operatorname{Spec} A$ be a separated morphism of schemes, let $p : V' \to P$ be a separated morphism, and let $K'$ be an ordered affine cover of $V'$, i.e. a finite linearly ordered index set $K'.\iota$ together with affine opens $K'.U\,i \subseteq V'$ whose supremum is $\top$. Let $F$ be an `OModulePresheaf` for $q$ and $F'$ one for $p \gg q$; such a datum assigns to every open $U$ an abelian group with compatible $A$-module and $\Gamma$-module structures forming a scalar tower, together with $A$-linear restriction maps that are semilinear over the restriction of sections and satisfy the reflexivity and composition identities. Suppose given, for every affine open $U$ of $P$, every affine open $V$ of $V'$ and every proof $h : V \le p^{-1}U$, an $A$-linear map $\eta_{U,V,h} : F(U) \to F'(V)$, such that: (i) $\eta_{U,V,h}(a \cdot x) = (p.\mathrm{appLE}\,U\,V\,h)(a) \cdot \eta_{U,V,h}(x)$ for $a \in \Gamma(P,U)$; (ii) for $V_1 \le V_2$ both inside $p^{-1}U$, restriction of $\eta_{U,V_2}(x)$ to $V_1$ is $\eta_{U,V_1}(x)$; (iii) for $U_1 \le U_2$ and $V$ inside both preimages, $\eta_{U_2,V}(x) = \eta_{U_1,V}(F.\mathrm{res}\,x)$. Then there is an affine-open morphism $v$ from $F$ to the Čech pushforward `cechPushforward p q K' F'`, whose value at an affine open $U$ lies in the module of families $(y_j)_j$ with $y_j \in F'(K'.U\,j \sqcap p^{-1}U)$ agreeing on pairwise intersections, such that for all affine $U$, all $x \in F(U)$ and all $j$ the $j$-th component of $v.\mathrm{app}\,U\,x$ is $\eta$ evaluated at $U$, the affine open $K'.U\,j \sqcap p^{-1}U$ and $x$.
--
--   This is the unit of the adjunction between inverse and direct image, written for the project's presheaf-of-modules data and for the Čech description of the direct image along $p$ relative to the cover $K'$: a coherent semilinear family of maps $F(U) \to F'(V)$ is exactly a morphism $F \to p_*F'$ in this setting. It is used in the statement asserting coherence and the description of kernels as $\mathfrak{p}$-power multiples of the whole module for proper morphisms over adically complete bases, where an adic system is compared with the direct image of its pull-back along a cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
    {A : Type u} [CommRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
    (F : OModulePresheaf q) (F' : OModulePresheaf (p ≫ q))
    (η : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (F.obj U.1 →ₗ[A] F'.obj V.1))
    (hηs : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : F.obj U.1),
      η U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η U V h x)
    (hηV : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
      (hV : V₁.1 ≤ V₂.1) (x : F.obj U.1), F'.res hV (η U V₂ h₂ x) = η U V₁ h₁ x)
    (hηU : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
      (hU : U₁.1 ≤ U₂.1) (x : F.obj U₂.1), η U₂ V h₂ x = η U₁ V h₁ (F.res hU x)) :
    ∃ v : OModulePresheaf.AffHom F (OModulePresheaf.cechPushforward p q K' F'),
      ∀ (U : P.affineOpens) (x : F.obj U.1) (j : K'.ι),
        (v.app U x).1 j = η U (OModulePresheaf.AffHom.affineChart p q K' U j)
          (OModulePresheaf.cechPushforward.chart_le_preimage p K' U.1 j) x := by sorry
