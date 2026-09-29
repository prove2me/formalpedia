-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_eq_of_isPullback_of_isPullback_of_three_le
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/608d85be-5632-5297-a315-bf710dd679d2
-- title:
--   Uniqueness of base-change comparison maps for level n≥ 3
-- statement:
--   Fix natural numbers $g,d,n$ with $3\le n$, commutative rings $S,S'$ (of type `Type`), a ring homomorphism $\varphi:S\to S'$ such that the image of $n$ in $S'$ is a unit, and polarised abelian schemes $u$ over $S$ and $u'$ over $S'$ with invariants $(g,d,n)$; thus each consists of a scheme with a structure morphism to the spectrum of the base ring, a commutative relative group law on its functor of points, the property bundle (smooth, proper, connected fibres, a group law exists), all fibres of topological Krull dimension $g$, a family $P_i$, $i\in\mathrm{Fin}(2g)$, of sections killed by $n$ which are independent and span the $n$-torsion over every algebraically closed field, and an invertible module `pol` defining a closed immersion by sections over the base whose $H^0$ on every geometric fibre has rank $d$. Let $g_1,g_2 : u'.A \to u.A$ be two morphisms such that, for $k=1,2$: the square formed by $g_k$, $u'.f$, $u.f$ and $\operatorname{Spec}\varphi$ is a pullback; composing with $g_k$ carries the product of any two $T$-points of $u'$ over $t'$ to the product, over $t'$ followed by $\operatorname{Spec}\varphi$, of their images; $(u'.P\,i)$ followed by $g_k$ equals $\operatorname{Spec}\varphi$ followed by $(u.P\,i)$ for every $i$; and the pullback of $u.pol$ along $g_k$ is isomorphic to $u'.pol$. Then $g_1 = g_2$.
--
--   This is the rigidity of the moduli problem of polarised abelian schemes with full level structure of level $n\ge 3$: such an object admits no non-trivial automorphism, so a base change is comparable to its source in at most one way. It is used in the construction of quasi-modular structures and in showing that the associated functor is formally unramified, and to see that an isomorphism of polarised abelian schemes over a fixed base is the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_eq_of_isPullback_of_isPullback_of_three_le.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le
    {g d n : ℕ} (hn : 3 ≤ n) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (hn' : IsUnit ((n : ℕ) : S'))
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
    (g₁ g₂ : u'.A ⟶ u.A)
    (h₁ : CategoryTheory.IsPullback g₁ u'.f u.f (Spec.map (CommRingCat.ofHom φ)))
    (h₁mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).1 ≫ g₁ =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ g₁, by rw [Category.assoc, h₁.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g₁, by rw [Category.assoc, h₁.w, ← Category.assoc, y.2]⟩).1)
    (h₁P : ∀ i, (u'.P i).1 ≫ g₁ = Spec.map (CommRingCat.ofHom φ) ≫ (u.P i).1)
    (h₁pol : Nonempty ((Scheme.Modules.pullback g₁).obj u.pol ≅ u'.pol))
    (h₂ : CategoryTheory.IsPullback g₂ u'.f u.f (Spec.map (CommRingCat.ofHom φ)))
    (h₂mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).1 ≫ g₂ =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ g₂, by rw [Category.assoc, h₂.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g₂, by rw [Category.assoc, h₂.w, ← Category.assoc, y.2]⟩).1)
    (h₂P : ∀ i, (u'.P i).1 ≫ g₂ = Spec.map (CommRingCat.ofHom φ) ≫ (u.P i).1)
    (h₂pol : Nonempty ((Scheme.Modules.pullback g₂).obj u.pol ≅ u'.pol)) :
    g₁ = g₂ := by sorry
