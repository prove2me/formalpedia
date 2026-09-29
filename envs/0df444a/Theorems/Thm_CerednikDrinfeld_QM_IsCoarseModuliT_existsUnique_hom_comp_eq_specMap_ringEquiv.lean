-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_hom_comp_eq_specMap_ringEquiv
-- name    : CerednikDrinfeld.QM.IsCoarseModuliT.existsUnique_hom_comp_eq_specMap_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/764bade2-7132-56ef-b1f8-786dfe9f6065
-- title:
--   Base automorphisms act on a coarse moduli scheme
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N$ and $\ell$, and a commutative ring $K$. Let $\mathcal{Y}$ be a scheme (in universe $0$) with a morphism $g : \mathcal{Y} \to \operatorname{Spec} K$, and let $\mathrm{pt}_T$ assign, to each commutative ring $S$, each morphism $s : \operatorname{Spec} S \to \operatorname{Spec} K$ and each object $u$ of `FakeEllipticCurve.WithExtraLevel` $\Lambda$ $N$ $\ell$ $S$ — that is, a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ structure together with an extra level structure at $\ell$ — a morphism $\mathcal{Y}$-ward from $\operatorname{Spec} S$ over $g$, i.e. a morphism $\operatorname{Spec} S \to \mathcal{Y}$ whose composite with $g$ is $s$. Assume `IsCoarseModuliT` for the data $(\mathcal{Y}, g, \mathrm{pt}_T)$: $\mathrm{pt}_T$ is invariant under isomorphism of objects, compatible with base change along ring homomorphisms in the sense of the pullback predicate for these objects, bijective on objects over algebraically closed fields up to isomorphism, and universal among all such point-assignments over $\operatorname{Spec} K$. Let $\tau$ be a ring automorphism of $K$. Then there is a unique morphism $h : \mathcal{Y} \to \mathcal{Y}$ such that $h$ followed by $g$ equals $g$ followed by $\operatorname{Spec}(\tau)$, and such that for every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec} K$ and every object $u$ over $S$, the underlying morphism of $\mathrm{pt}_T(S, s \circ \operatorname{Spec}(\tau), u)$ equals the underlying morphism of $\mathrm{pt}_T(S, s, u)$ followed by $h$.
--
--   This is the standard statement that automorphisms of the base ring act on a coarse moduli scheme, here for the moduli problem of fake elliptic curves with $\Lambda$-action, level $N$ and extra level at $\ell$; the action is pinned down both by the base morphism it lies over and by its effect on moduli points. It is used by [`CerednikDrinfeld.QM.exists_galT_of_coarse_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.exists_galT_of_coarse_of_two_mul_dvd) to produce Galois-type automorphisms of the moduli scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_hom_comp_eq_specMap_ringEquiv.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsCoarseModuliT.existsUnique_hom_comp_eq_specMap_ringEquiv
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) {K : Type} [CommRing K]
    (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of K))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of K)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g)
    (hco : IsCoarseModuliT Λ N ℓ 𝒴 g ptT) (τ : K ≃+* K) :
    ∃! h : 𝒴 ⟶ 𝒴, h ≫ g = g ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K)) ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of K))
        (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (ptT S (s ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) u).1 = (ptT S s u).1 ≫ h := by sorry
