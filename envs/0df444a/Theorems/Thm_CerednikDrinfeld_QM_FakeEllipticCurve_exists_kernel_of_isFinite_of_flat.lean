-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernel_of_isFinite_of_flat
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernel_of_isFinite_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/0f8e2fd2-42f7-5007-acd4-cee8eefca58b
-- title:
--   Finite flat kernel of a morphism of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a commutative ring $S$. Let $\mathcal{A}$ and $\mathcal{D}$ be two objects of type `FakeEllipticCurve Λ N S`, so each consists of a scheme ($\mathcal{A}.A$, resp. $\mathcal{D}.A$) with a structure morphism to $\operatorname{Spec} S$ ($\mathcal{A}.f$, resp. $\mathcal{D}.f$), a commutative relative group law on its functor of points over $\operatorname{Spec} S$, a bundle of properties asserting that the structure morphism is smooth, proper, with connected fibres and admitting a relative group law, fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over $\operatorname{Spec} S$ compatible with the group law and subject to a trace condition on tangent spaces, together with the remaining data of that structure. Let $\Phi : \mathcal{A}.A \to \mathcal{D}.A$ be a morphism with $\Phi$ followed by $\mathcal{D}.f$ equal to $\mathcal{A}.f$, and assume $\Phi$ is finite, flat and locally of finite presentation. Then there exist a scheme $Kk$ and a morphism $\iota : Kk \to \mathcal{A}.A$ such that: $\iota$ is a closed immersion; $\iota$ followed by $\mathcal{A}.f$ is finite, flat and locally of finite presentation; for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every $P : T \to \mathcal{A}.A$ with $P$ followed by $\mathcal{A}.f$ equal to $t$, there is a factorisation $P = \iota \circ P_0$ for some $P_0 : T \to Kk$ if and only if $P$ followed by $\Phi$ is the unit $T$-point $\mathcal{D}.L.\mathrm{one}\,t$ of the group law of $\mathcal{D}$; and for every point $s$ of $\operatorname{Spec} S$, the flat rank of $\iota$ followed by $\mathcal{A}.f$ at $s$ equals the flat rank of $\Phi$ at the image of $s$ under the underlying continuous map of the unit section $\mathcal{D}.L.\mathrm{one}\,(\mathrm{id})$.
--
--   This is the construction of the scheme-theoretic kernel of a finite flat homomorphism of fake elliptic curves as a finite flat closed subscheme of the source, characterised by its functor of points and with rank equal to the degree of $\Phi$ along the unit section. It is used in the study of extra levels on fake elliptic curves, in particular by [`CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_or_forall_reducesToZero_of_extraLevels`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_or_forall_reducesToZero_of_extraLevels), [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem) and [`CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_finrank_of_isClosedImmersion_kernel`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_finrank_of_isClosedImmersion_kernel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernel_of_isFinite_of_flat.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernel_of_isFinite_of_flat
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S] (𝒜 𝒟 : FakeEllipticCurve Λ N S)
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f) [IsFinite Φ] [Flat Φ] [LocallyOfFinitePresentation Φ] :
    ∃ (Kk : Scheme.{u}) (ι : Kk ⟶ 𝒜.A),
      IsClosedImmersion ι ∧ IsFinite (ι ≫ 𝒜.f) ∧ Flat (ι ≫ 𝒜.f) ∧ LocallyOfFinitePresentation (ι ≫ 𝒜.f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t 𝒜.f),
        FactorsThrough ι P ↔ mapPt Φ hΦ P = 𝒟.L.one t) ∧
      (∀ s : ↥(Spec (CommRingCat.of S)),
        (ι ≫ 𝒜.f).finrank s = Φ.finrank ((𝒟.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s)) := by sorry
