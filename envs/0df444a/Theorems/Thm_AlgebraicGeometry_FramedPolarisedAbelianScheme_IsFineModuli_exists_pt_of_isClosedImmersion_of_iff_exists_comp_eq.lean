-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_IsFineModuli_exists_pt_of_isClosedImmersion_of_iff_exists_comp_eq
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.IsFineModuli.exists_pt_of_isClosedImmersion_of_iff_exists_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/0661660f-364d-5aef-8160-2b2220c3e035
-- title:
--   Closed Theta-locus in a framed fine moduli scheme
-- statement:
--   Fix naturals $g,N,n$, a commutative ring $B$, a scheme $H$ with a morphism $\pi_H\colon H\to\operatorname{Spec}B$, and an assignment $\mathrm{pt}_H$ which, for every commutative ring $S$, every $s\colon\operatorname{Spec}S\to\operatorname{Spec}B$ and every framed polarised abelian scheme $X$ over $S$ of invariants $(g,N,n)$ — a commutative relative group scheme $A\to\operatorname{Spec}S$ with abelian-scheme property bundle, fibres of dimension $g$, $2g$ sections generating the $n$-torsion freely, and an invertible very ample polarisation module of geometric fibre rank $N+1$, equipped with a `ProjPresentation` whose map to $\operatorname{Proj}$ over $B$-variables is a closed immersion and whose sections form a section basis — returns a morphism $\operatorname{Spec}S\to H$ over $s$. Assume $\mathrm{pt}_H$ is a fine moduli datum: constant on `Iso`-classes, compatible with pullback along ring maps `IsPullback`, surjective onto $S$-points of $H$ over $s$, and injective up to `Iso`. Assume $\pi_H$ is separated, quasi-compact and locally of finite presentation, that every finite set of points of $H$ lies in one affine open, and that $H$ admits an immersion into some $\operatorname{Proj}$ of $B$-polynomials over $\operatorname{Spec}B$ compatible with $\pi_H$. Let $\Theta$ be a predicate on framed objects, and $\iota\colon H_\Theta\to H$ a closed immersion locally of finite presentation such that $\Theta(S,X)$ holds precisely when $\mathrm{pt}_H(S,s,X)$ factors through $\iota$, for all $S,s,X$. Then there is $\mathrm{pt}_\Theta$, assigning to each $\Theta$-object a morphism over $\iota\circ\pi_H$ whose composite with $\iota$ is $\mathrm{pt}_H$, which is constant on `Iso`-classes, compatible with pullback, surjective onto $S$-points of $H_\Theta$ over $s$ and injective up to `Iso`; moreover $\iota$ followed by $\pi_H$ is separated, quasi-compact and locally of finite presentation, every finite set of points of $H_\Theta$ lies in one affine open, and $H_\Theta$ admits an immersion into a $\operatorname{Proj}$ of $B$-polynomials compatible with $\iota$ followed by $\pi_H$.
--
--   This is the representability of a closed subfunctor of a representable moduli functor: the locus where a condition $\Theta$ on framed polarised abelian schemes holds is again a fine moduli scheme, inheriting separatedness, quasi-compactness, finite presentation, the affine-open property for finite sets of points and quasi-projectivity over $B$. It is used to construct the fine moduli scheme for the $\Theta$-condition on the theta-device route to modularity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_IsFineModuli_exists_pt_of_isClosedImmersion_of_iff_exists_comp_eq.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.IsFineModuli.exists_pt_of_isClosedImmersion_of_iff_exists_comp_eq
    (g N n : ℕ) (B : Type) [CommRing B]
    (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of B))
    (ptH : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FramedPolarisedAbelianScheme g N n S → SchemeHomOver s πH)
    (hH : FramedPolarisedAbelianScheme.IsFineModuli g N n H πH ptH)
    (hsep : IsSeparated πH) (hqc : QuasiCompact πH) (hfp : LocallyOfFinitePresentation πH)
    (hAF : ∀ F : Finset H, ∃ U : H.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (hQP : (∃ (qpm : ℕ) (qpι : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpm + 1)) B)), IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpm = πH))
    (Θ : ∀ (S : Type) [CommRing S], FramedPolarisedAbelianScheme g N n S → Prop)
    (HΘ : Scheme.{0}) (ι : HΘ ⟶ H) (hι : IsClosedImmersion ι) (hιfp : LocallyOfFinitePresentation ι)
    (hΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (X : FramedPolarisedAbelianScheme g N n S),
      Θ S X ↔ ∃ y : Spec (CommRingCat.of S) ⟶ HΘ, y ≫ ι = (ptH S s X).1) :
    ∃ (ptΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (X : FramedPolarisedAbelianScheme g N n S), Θ S X → SchemeHomOver s (ι ≫ πH)),
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X), (ptΘ S s X hX).1 ≫ ι = (ptH S s X).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'),
        FramedPolarisedAbelianScheme.Iso X X' → ptΘ S s X hX = ptΘ S s X' hX') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S') (hX : Θ S X) (hX' : Θ S' X'),
        FramedPolarisedAbelianScheme.IsPullback φ X X' →
        (ptΘ S' s' X' hX').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptΘ S s X hX).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s (ι ≫ πH)),
        ∃ (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X), ptΘ S s X hX = x) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'), ptΘ S s X hX = ptΘ S s X' hX' →
        FramedPolarisedAbelianScheme.Iso X X') ∧
      IsSeparated (ι ≫ πH) ∧ QuasiCompact (ι ≫ πH) ∧ LocallyOfFinitePresentation (ι ≫ πH) ∧
      (∀ F : Finset HΘ, ∃ U : HΘ.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
      (∃ (qpn : ℕ) (qpι : HΘ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) B)),
        IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpn = ι ≫ πH) := by sorry
