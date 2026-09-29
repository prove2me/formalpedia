-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing
-- name    : AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/c2a96b8f-08e9-5a48-b1c9-d646eda5db58
-- title:
--   Finite quotients are quotients for π-nilpotent point functors
-- statement:
--   Let $\mathcal O$ be a Noetherian commutative ring and $\pi \in \mathcal O$. Let $f_M : M \to \operatorname{Spec}\mathcal O$ and $f : X \to \operatorname{Spec}\mathcal O$ be morphisms of schemes, both locally of finite type, let $G$ be a finite group and $\rho : G \to \operatorname{Aut}(M)$ a homomorphism with $\rho(g)$ commuting with $f_M$ for all $g$, and let $p : M \to X$ satisfy $p$ followed by $f$ equals $f_M$, be $G$-invariant ($\rho(g)$ followed by $p$ equals $p$), integral, affine, surjective on points, and be such that for every open $V \subseteq X$ the map $p^\sharp$ on sections over $V$ is injective with image exactly the sections of $\mathcal O_M$ over $p^{-1}V$ fixed by all $\rho(g)$. For $h : Y \to \operatorname{Spec}\mathcal O$ write $Y(B)$ for the set of morphisms $\operatorname{Spec} B \to Y$ over $\mathcal O$, a functor of the $\mathcal O$-algebra $B$ via precomposition. Let $t : T \to \operatorname{Spec}\mathcal O$ be a further $\mathcal O$-scheme and let $u$ assign, to every $\mathcal O$-algebra $B$ in which $\pi$ is nilpotent, a map $M(B) \to T(B)$, compatible with $\mathcal O$-algebra maps $B \to B'$ and invariant under composing with each $\rho(g)$. Then there exists a family $\bar u : X(B) \to T(B)$ on such $B$, compatible with $\mathcal O$-algebra maps, with $\bar u_B(\varphi \circ p) = u_B(\varphi)$ for all $\varphi \in M(B)$ — where $\varphi \circ p$ denotes $\varphi$ followed by $p$ — and any further compatible family $u'$ with the same property agrees with $\bar u$ at every such $B$ and every point of $X(B)$.
--
--   This is the statement that the quotient presentation $p : M \to X$ of a scheme by a finite group action remains a quotient after restriction to the functor of points on $\mathcal O$-algebras in which $\pi$ is nilpotent: $G$-invariant natural families on $M$ descend uniquely to $X$. It is obtained from the corresponding affine-over-affine statement, and is used in the Čerednik–Drinfeld uniformisation steps for quaternionic moduli, both in the coarse and in the fine moduli formulations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] (π : 𝒪)
    {M X : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (f : X ⟶ Spec (CommRingCat.of 𝒪))
    (hlft : LocallyOfFiniteType fM) (hlftX : LocallyOfFiniteType f)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut M) (hover : ∀ g : G, (ρ g).hom ≫ fM = fM)
    (p : M ⟶ X) (hp : p ≫ f = fM) (hρp : ∀ g : G, (ρ g).hom ≫ p = p)
    (hint : IsIntegralHom p) (haff : IsAffineHom p) (hsurj : Function.Surjective p.base)
    (hsec : ∀ V : X.Opens, Function.Injective (p.app V))
    (hinv : ∀ V : X.Opens, Set.range (p.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hρp g]) s = s})
    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints fM).obj B → (Scheme.nilpPoints t).obj B)
    (hu_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints fM).obj B), u B' hB' ((Scheme.nilpPoints fM).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x))
    (hu_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : G) (y : (Scheme.nilpPoints fM).obj B),
      u B hB ((Scheme.nilpPoints.mapHom fM fM (ρ g).hom (hover g)).app B y) = u B hB y) :
    ∃ ubar : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), ubar B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (ubar B hB x)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fM).obj B),
        ubar B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) = u B hB y) ∧
      ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u' B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fM).obj B),
          u' B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) = u B hB y) →
        ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints f).obj B), u' B hB z = ubar B hB z := by sorry
