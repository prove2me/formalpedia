-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural
-- name    : AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/912349d7-7fed-509c-8ca2-99752ddf3eaa
-- title:
--   Yoneda on Noetherian test algebras over a Noetherian base
-- statement:
--   Let $\mathcal{O}$ be a Noetherian commutative ring, let $X$ and $Y$ be schemes (in the bottom universe), and let $fX : X \to \operatorname{Spec}\mathcal{O}$ and $fY : Y \to \operatorname{Spec}\mathcal{O}$ be morphisms, with $fX$ locally of finite type. For a commutative $\mathcal{O}$-algebra $B$, write $X(B)$ for the set `(Scheme.nilpPoints fX).obj B`, namely the pairs consisting of a morphism $\varphi : \operatorname{Spec} B \to X$ together with a proof that $\varphi$ followed by $fX$ equals $\operatorname{Spec}$ of the structure map $\mathcal{O} \to B$; for an $\mathcal{O}$-algebra homomorphism $g : B \to B'$ the functorial action sends $\varphi$ to $\operatorname{Spec}(g)$ followed by $\varphi$, and similarly for $fY$. Assume given, for every Noetherian commutative $\mathcal{O}$-algebra $B$, a map $\tau_B : X(B) \to Y(B)$, and assume naturality: for all Noetherian $\mathcal{O}$-algebras $B, B'$, every $\mathcal{O}$-algebra homomorphism $g : B \to B'$ and every $\varphi \in X(B)$, one has $\tau_{B'}(g_*\varphi) = g_*(\tau_B \varphi)$. The conclusion is that there is a unique morphism $h : X \to Y$ such that $h$ followed by $fY$ equals $fX$ and, for every Noetherian $\mathcal{O}$-algebra $B$ and every $\varphi \in X(B)$, the underlying morphism of $\tau_B\varphi$ equals $\varphi$ followed by $h$; uniqueness is asserted for the conjunction of these two properties.
--
--   This is the Yoneda-type representability statement restricted to Noetherian test algebras: a natural transformation of functors of points defined only on Noetherian $\mathcal{O}$-algebras is induced by a unique morphism of schemes over $\mathcal{O}$, provided the source is locally of finite type over a Noetherian base. It is used in the Čerednik–Drinfeld part of the development, for instance in establishing bijectivity criteria for maps of moduli functors and injectivity properties of period maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪]
    {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of 𝒪)) (fY : Y ⟶ Spec (.of 𝒪)) [LocallyOfFiniteType fX]
    (τ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [IsNoetherianRing B],
      (Scheme.nilpPoints fX).obj B → (Scheme.nilpPoints fY).obj B)
    (hτ : ∀ (B B' : Type) [CommRing B] [Algebra 𝒪 B] [IsNoetherianRing B] [CommRing B'] [Algebra 𝒪 B'] [IsNoetherianRing B']
      (g : B →ₐ[𝒪] B') (φ : (Scheme.nilpPoints fX).obj B),
      τ B' ((Scheme.nilpPoints fX).map g φ) = (Scheme.nilpPoints fY).map g (τ B φ)) :
    ∃! h : X ⟶ Y, h ≫ fY = fX ∧
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [IsNoetherianRing B] (φ : (Scheme.nilpPoints fX).obj B),
        (τ B φ).1 = φ.1 ≫ h := by sorry
