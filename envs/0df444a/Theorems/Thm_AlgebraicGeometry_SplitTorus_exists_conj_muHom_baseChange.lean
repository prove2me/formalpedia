-- Prove2me | Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_conj_muHom_baseChange
-- name    : AlgebraicGeometry.SplitTorus.exists_conj_muHom_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/13a02a2b-6517-54bb-b2f7-6ca4c038a08a
-- title:
--   Conjugating a toric morphism by an automorphism of A
-- statement:
--   Let $R_0$ be a commutative ring, let $A$ be a commutative local ring, let $\sigma\colon \operatorname{Spec} A \to \operatorname{Spec} R_0$ be a morphism of schemes, let $s$ be a ring automorphism of $A$ such that $\operatorname{Spec}(s)$ followed by $\sigma$ equals $\sigma$, and let $\bar s$ be a ring endomorphism of the residue field of $A$ with $\bar s \circ \mathrm{res} = \mathrm{res} \circ s$. Let $g\colon G \to \operatorname{Spec} R_0$ be a scheme over $R_0$ equipped with a relative group law $L$, that is, a group structure on the sets of sections $\{\varphi : T \to G \mid \varphi \text{ over } t\}$ for all test schemes $t\colon T \to \operatorname{Spec} R_0$, natural in $T$. For $t, m \in \mathbb{N}$ write $\mu_{B} := \operatorname{Spec} B[(\mathbb{Z}/m)^{t}]$ for the spectrum of the monoid algebra on $\mathrm{Fin}\,t \to \mathbb{Z}/m$ over a ring $B$, with its structure map to $\operatorname{Spec} B$, and for a ring homomorphism $\varphi$ let `muBaseChange` $\varphi$ be the induced morphism of such spectra. Given a morphism $\iota\colon \mu_A \to G \times_{\operatorname{Spec} R_0} \operatorname{Spec} A$ commuting with the structure maps (i.e. $\iota$ followed by the second projection is the structure map of $\mu_A$), the assertion is that there exists such a morphism $\iota'$ with: (i) $\iota'$ followed by the first projection to $G$ equals `muBaseChange` $s$ followed by $\iota$ followed by that projection; (ii) if $\iota$ is multiplicative on points in the sense that for every $A$-algebra $S$ and all $\chi, \chi'$ in `WithConv` of the $A$-algebra homomorphisms $A[(\mathbb{Z}/m)^{t}] \to S$ the point $\chi\chi'$ of $\mu_A$ composed with $\iota$ is the product, under the base-changed law $L$ over $A$, of the compositions of $\iota$ with the points $\chi$ and $\chi'$, then the same holds for $\iota'$; (iii) if $\iota$ is a closed immersion, so is $\iota'$; and (iv) `muBaseChange` $(\mathrm{res})$ followed by $\iota'$ and the projection to $G$ equals `muBaseChange` $(\bar s)$ followed by `muBaseChange` $(\mathrm{res})$, $\iota$ and that projection.
--
--   This is the construction of the conjugate $\iota^{s}$ of a morphism from a split group of multiplicative type into the base change $G \times_{R_0} A$, by an automorphism $s$ of $A$ over $R_0$: the conjugate again respects the group law on points, remains a closed immersion, and its special fibre is the original special fibre precomposed with the residual automorphism $\bar s$. It is used, together with uniqueness of toric lifts over a henselian base, to construct the action of a decomposition or inertia group on toric lifts in the Néron models of modular Jacobians, and is cited in the treatment of the $J_0$ and $J_H$ Néron objects at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SplitTorus_exists_conj_muHom_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SplitTorus IsLocalRing

theorem AlgebraicGeometry.SplitTorus.exists_conj_muHom_baseChange
    {R₀ : Type u} [CommRing R₀] {A : Type u} [CommRing A] [IsLocalRing A]
    (σ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R₀))
    (s : A ≃+* A) (hs : Spec.map (CommRingCat.ofHom s.toRingHom) ≫ σ = σ)

    (sbar : ResidueField A →+* ResidueField A) (hsbar : sbar.comp (residue A) = (residue A).comp s.toRingHom)
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R₀)) (L : RelativeGroupLaw R₀ g)
    (t m : ℕ) (ι : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g)) :
    ∃ ι' : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g),

      ι'.1 ≫ pullback.fst g σ = muBaseChange s.toRingHom t m ≫ ι.1 ≫ pullback.fst g σ ∧

      ((∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
          NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι =
            (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι)
              (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι)) →
        ∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
          NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι' =
            (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι')
              (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι')) ∧

      (IsClosedImmersion ι.1 → IsClosedImmersion ι'.1) ∧

      muBaseChange (residue A) t m ≫ ι'.1 ≫ pullback.fst g σ =
        muBaseChange sbar t m ≫ muBaseChange (residue A) t m ≫ ι.1 ≫ pullback.fst g σ := by sorry
