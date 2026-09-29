-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_exists_subalgebra_fg_map_eq_of_locallyOfFiniteType
-- name    : AlgebraicGeometry.Scheme.nilpPoints.exists_subalgebra_fg_map_eq_of_locallyOfFiniteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/a3bad063-8e13-5c10-be38-322713d56cd9
-- title:
--   Points factor through finitely generated subalgebras
-- statement:
--   Let $\mathcal{O}$ be a Noetherian commutative ring, let $R$ be a commutative $\mathcal{O}$-algebra, and let $f \colon X \to \operatorname{Spec}\mathcal{O}$ be a morphism of schemes that is locally of finite type. Write $X(B)$ for the value at a commutative $\mathcal{O}$-algebra $B$ of the functor `Scheme.nilpPoints f`, namely the set of morphisms $\varphi \colon \operatorname{Spec} B \to X$ such that $\varphi$ followed by $f$ equals $\operatorname{Spec}$ of the structure map $\mathcal{O} \to B$; for an $\mathcal{O}$-algebra homomorphism $g$, the induced map on points is composition of $\operatorname{Spec} g$ with $\varphi$. The assertion is the conjunction of two statements, each quantified over all commutative rings $B$ equipped with $\mathcal{O}$-algebra and $R$-algebra structures forming a scalar tower over $\mathcal{O}$, $R$, $B$. First: every $y \in X(B)$ is the image of some $y_0 \in X(S)$ under the map induced by the inclusion of some $R$-subalgebra $S \subseteq B$ that is finitely generated as an $R$-algebra (the inclusion being read as a homomorphism of $\mathcal{O}$-algebras). Second: if $S_1, S_2 \subseteq B$ are finitely generated $R$-subalgebras and $y_1 \in X(S_1)$, $y_2 \in X(S_2)$ have the same image in $X(B)$, then there is a finitely generated $R$-subalgebra $S_3 \subseteq B$ with $S_1 \le S_3$ and $S_2 \le S_3$ such that $y_1$ and $y_2$ already have the same image in $X(S_3)$ under the maps induced by the two inclusions.
--
--   Together the two clauses say that $X(B) = \varinjlim_S X(S)$ over the directed system of finitely generated $R$-subalgebras $S$ of $B$, the form for this points functor of the Grothendieck limit theorem for schemes locally of finite presentation over a Noetherian base (EGA IV, 8.14.2). It supplies the surjectivity and injectivity inputs used to extend morphisms and uniformisation data from Noetherian test algebras, where finitely generated algebras over $\mathcal{O}$ are Noetherian, to arbitrary test algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_nilpPoints_exists_subalgebra_fg_map_eq_of_locallyOfFiniteType.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

theorem AlgebraicGeometry.Scheme.nilpPoints.exists_subalgebra_fg_map_eq_of_locallyOfFiniteType
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪]
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of 𝒪)) [LocallyOfFiniteType f] :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra R B] [IsScalarTower 𝒪 R B] (y : (Scheme.nilpPoints f).obj B),
        ∃ (S : Subalgebra R B) (_ : S.FG) (y₀ : (Scheme.nilpPoints f).obj ↥S),
          (Scheme.nilpPoints f).map ((S.val).restrictScalars 𝒪) y₀ = y) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra R B] [IsScalarTower 𝒪 R B]
        (S₁ S₂ : Subalgebra R B), S₁.FG → S₂.FG →
        ∀ (y₁ : (Scheme.nilpPoints f).obj ↥S₁) (y₂ : (Scheme.nilpPoints f).obj ↥S₂),
        (Scheme.nilpPoints f).map ((S₁.val).restrictScalars 𝒪) y₁ = (Scheme.nilpPoints f).map ((S₂.val).restrictScalars 𝒪) y₂ →
        ∃ (S₃ : Subalgebra R B) (_ : S₃.FG) (h₁ : S₁ ≤ S₃) (h₂ : S₂ ≤ S₃),
          (Scheme.nilpPoints f).map ((Subalgebra.inclusion h₁).restrictScalars 𝒪) y₁ =
            (Scheme.nilpPoints f).map ((Subalgebra.inclusion h₂).restrictScalars 𝒪) y₂) := by sorry
