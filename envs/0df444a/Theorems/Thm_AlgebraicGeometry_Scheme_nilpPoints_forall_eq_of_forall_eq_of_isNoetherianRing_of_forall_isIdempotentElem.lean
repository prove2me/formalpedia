-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_forall_eq_of_forall_eq_of_isNoetherianRing_of_forall_isIdempotentElem
-- name    : AlgebraicGeometry.Scheme.nilpPoints.forall_eq_of_forall_eq_of_isNoetherianRing_of_forall_isIdempotentElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/ab468369-0b4a-519c-b2f2-6f93e5cff6c1
-- title:
--   Noetherian approximation of natural families of π-adic points
-- statement:
--   Let $\mathcal O$ be a commutative ring, $\pi \in \mathcal O$, and let $F$ be an `AlgFunctor` over $\mathcal O$, i.e. an assignment of a type $F(B)$ to every commutative $\mathcal O$-algebra $B$ (in the base universe) together with maps $F(\varphi) : F(B) \to F(B')$ for $\mathcal O$-algebra homomorphisms $\varphi$, compatible with identities and composition. Let $f_N : N \to \operatorname{Spec} \mathcal O$ be a scheme over $\operatorname{Spec}\mathcal O$, so that `Scheme.nilpPoints` $f_N$ assigns to each $\mathcal O$-algebra $B$ the set of morphisms $\varphi : \operatorname{Spec} B \to N$ with $\varphi$ followed by $f_N$ equal to $\operatorname{Spec}$ of the structure map $\mathcal O \to B$, functorially in $B$. Assume: (i) for every $B$ in which the image of $\pi$ is nilpotent and every $x \in F(B)$ there are an $\mathcal O$-subalgebra $S \subseteq B$ with $S$ a Noetherian ring and $x_0 \in F(S)$ whose image under $F$ of the inclusion is $x$; (ii) $u_1, u_2$ assign, to each such $B$, a nilpotency witness for the image of $\pi$, and each $x \in F(B)$, a morphism $\operatorname{Spec} B \to N$ over $\operatorname{Spec}\mathcal O$; (iii) both families are natural: for every $\mathcal O$-algebra map $\varphi : B \to B'$ between $\pi$-nilpotent algebras and every $x \in F(B)$, $u_i(F(\varphi)(x))$ equals the image of $u_i(x)$ under precomposition with $\operatorname{Spec}\varphi$; (iv) $u_1$ and $u_2$ agree on all $x \in F(B)$ whenever $B$ is Noetherian, $\pi$-nilpotent and has no idempotents besides $0$ and $1$. Then $u_1$ and $u_2$ agree on $F(B)$ for every $\mathcal O$-algebra $B$ in which the image of $\pi$ is nilpotent.
--
--   This is the descent step used to pass from a rigidity statement over Noetherian test algebras with connected spectrum to all $\pi$-nilpotent test algebras; it is applied in the construction and uniqueness of extensions of natural transformations to the functor of points of the formal scheme attached to $\Omega$ in the Čerednik–Drinfel'd setting, and is cited by the uniqueness and equivariance results for those extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_nilpPoints_forall_eq_of_forall_eq_of_isNoetherianRing_of_forall_isIdempotentElem.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

theorem AlgebraicGeometry.Scheme.nilpPoints.forall_eq_of_forall_eq_of_isNoetherianRing_of_forall_isIdempotentElem
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (F : AlgFunctor 𝒪)
    {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))

    (hF : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → ∀ x : F.obj B,
      ∃ (S : Subalgebra 𝒪 B) (_ : IsNoetherianRing ↥S) (x₀ : F.obj ↥S), F.map S.val x₀ = x)

    (u₁ u₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints fN).obj B)
    (hu₁ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : F.obj B),
      u₁ B' hB' (F.map φ x) = (Scheme.nilpPoints fN).map φ (u₁ B hB x))
    (hu₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : F.obj B),
      u₂ B' hB' (F.map φ x) = (Scheme.nilpPoints fN).map φ (u₂ B hB x))

    (heq : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)),
      (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → ∀ x : F.obj B, u₁ B hB x = u₂ B hB x) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u₁ B hB x = u₂ B hB x := by sorry
