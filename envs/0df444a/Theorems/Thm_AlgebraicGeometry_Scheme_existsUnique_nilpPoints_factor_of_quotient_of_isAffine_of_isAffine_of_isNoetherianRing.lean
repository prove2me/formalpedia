-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing
-- name    : AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/2afe2645-41fc-52b4-9c5f-6afd8a1e0fbe
-- title:
--   Descent of π-nilpotent point families along an affine finite quotient
-- statement:
--   Let $\mathcal O$ be a Noetherian commutative ring and $\pi \in \mathcal O$. Let $f_M : M \to \operatorname{Spec}\mathcal O$ and $f : X \to \operatorname{Spec}\mathcal O$ be morphisms of schemes, both locally of finite type, let $G$ be a finite group and $\rho : G \to \operatorname{Aut} M$ a homomorphism with each $\rho(g)$ commuting with $f_M$, and let $p : M \to X$ satisfy $p$ followed by $f$ equals $f_M$ and $\rho(g)$ followed by $p$ equals $p$ for all $g$. Assume $p$ is integral, affine and surjective on points, and that for every open $V \subseteq X$ the ring map $p^\ast$ on sections over $V$ is injective with image exactly the sections of $M$ over $p^{-1}V$ fixed by all the maps induced by $\rho(g)$. Let $t : T \to \operatorname{Spec}\mathcal O$ be a further scheme over $\mathcal O$. For an $\mathcal O$-algebra $B$, write $M(B)$ for the set of morphisms $\operatorname{Spec} B \to M$ over $\operatorname{Spec}\mathcal O$, and similarly $X(B)$, $T(B)$; these are functorial in $\mathcal O$-algebra maps by composition with the induced morphism of spectra. Suppose given maps $u_B : M(B) \to T(B)$ for all $B$ in which $\pi$ becomes nilpotent, compatible with $\mathcal O$-algebra maps $B \to B'$ and invariant under composing a point with $\rho(g)$. Assume finally that $X$ and $T$ are affine. Then there is a family $\bar u_B : X(B) \to T(B)$, on the same class of algebras, compatible with $\mathcal O$-algebra maps, satisfying $\bar u_B(\varphi \circ p) = u_B(\varphi)$ for every $\varphi \in M(B)$, and such that any compatible family $u'$ with the same factorisation property agrees with $\bar u$ at every $B$ and every point of $X(B)$.
--
--   This is the bi-affine case of the statement that a finite-group quotient $p : M \to X$, in the sense of being integral, affine, surjective and identifying the structure sheaf of $X$ with the $G$-invariants of that of $M$, is also a quotient for natural families of maps defined on points with values in $\mathcal O$-algebras in which $\pi$ is nilpotent. It feeds the general (non-affine) version [`AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing`](thm.html#AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing), obtained from it by localising on $X$, and the proof reduces the assertion, via $\pi^n$-truncations and Yoneda, to the ring-theoretic factorisation [`RingHom.existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing`](thm.html#RingHom.existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing
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
      u B hB ((Scheme.nilpPoints.mapHom fM fM (ρ g).hom (hover g)).app B y) = u B hB y)
    (hX : IsAffine X) (hT : IsAffine T) :
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
