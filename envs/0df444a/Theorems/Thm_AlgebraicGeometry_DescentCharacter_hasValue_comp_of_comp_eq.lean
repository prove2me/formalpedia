-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_comp_of_comp_eq
-- name    : AlgebraicGeometry.DescentCharacter.hasValue_comp_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/a2adc6f8-d2aa-50a1-8e50-97f381a758e0
-- title:
--   Descent character values multiply under composition
-- statement:
--   Let $X,Y$ be schemes (in a fixed universe), $R$ a commutative ring, and $f\colon X \to \operatorname{Spec}(R)$ a morphism of schemes. Let $T_1,T_2\colon X \to X$ and $q\colon X \to Y$ be morphisms, and assume $T_1$ followed by $q$ equals $q$, $T_2$ followed by $q$ equals $q$, that $T_1$ followed by $f$ equals $f$, and that ($T_1$ followed by $T_2$) followed by $q$ again equals $q$ (this last identity is taken as a hypothesis, so the composite is considered together with a chosen proof that it lies over $q$). Let $N,M$ be $\mathcal{O}_Y$-modules and let $\beta$ be an isomorphism from the pullback $q^{*}N$ to the pullback $q^{*}M$, and let $c_1,c_2 \in R$. For an endomorphism lying over $q$ via an identity $h$, the associated discrepancy is the automorphism of $q^{*}M$ given by $\beta^{-1}$ followed by the translate `translateIso h β` of $\beta$ along $h$; the assertion that $\beta$ has value $c$ at $h$ means that for every open $U \subseteq X$ and every section $s$ of $q^{*}M$ over $U$, the component at $U$ of that discrepancy sends $s$ to `baseSection f c U` $\cdot\, s$, the scalar attached to $c$ over $U$ by $f$. Under the hypotheses that $\beta$ has value $c_1$ at the identity for $T_1$ and value $c_2$ at the identity for $T_2$, the conclusion is that $\beta$ has value $c_1 c_2$ at the identity for $T_1$ followed by $T_2$.
--
--   This is the multiplicativity of the descent character attached to an isomorphism between pullbacks along $q$: the value of the character is a homomorphism in the deck transformation variable, the classical model being that for an abelian scheme, $q = [n]$ and $T$ a translation by an $n$-torsion point, one recovers the fact that $e_n$ is a homomorphism in each variable. It is used in the construction of torsion characters of order two associated with a polarisation, where a pullback of a module along multiplication by two is shown to carry such a character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentCharacter_hasValue_comp_of_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.hasValue_comp_of_comp_eq
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T₁ T₂ : X ⟶ X} {q : X ⟶ Y} (h₁ : T₁ ≫ q = q) (h₂ : T₂ ≫ q = q) (hT₁ : T₁ ≫ f = f)
    (h₁₂ : (T₁ ≫ T₂) ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (c₁ c₂ : R) (hβ₁ : HasValue f h₁ β c₁) (hβ₂ : HasValue f h₂ β c₂) :
    HasValue f h₁₂ β (c₁ * c₂) := by sorry
