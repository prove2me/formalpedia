-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_levelStructure_lev_comp_of_disjoint
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.levelStructure_lev_comp_of_disjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/5b34c658-e5aa-5ee3-9f5a-b852f9f14128
-- title:
--   Transport of a level structure along a finite homomorphism
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$, let $N\in\mathbb{N}$, let $S$ be a commutative ring and let $E$ be a `FakeEllipticCurve` for $\Lambda$, $N$ and $S$, with total space `E.A`, structure morphism `E.f` to $\operatorname{Spec} S$, relative group law `E.L`, $\Lambda$-action `E.act` and level morphism `E.lev` from `E.C`. Let $f' : A' \to \operatorname{Spec} S$ be a further scheme over $S$ carrying a relative group law $L'$ (a group structure on the sets of $T$-points over $\operatorname{Spec} S$, natural in $T$) assumed commutative, together with endomorphisms $\mathrm{act}'(x)$ of $A'$ over $\operatorname{Spec} S$ for $x \in \Lambda$. Let $p : E.A \to A'$ satisfy $p$ followed by $f'$ equals `E.f`, be finite, be a homomorphism on $T$-points for every $T$-base $t$, satisfy $p \circ E.act(x) = \mathrm{act}'(x) \circ p$ for all $x\in\Lambda$, and have the disjointness property that a $T$-point $P$ of `E.f` with $p(P)$ the identity and factoring through `E.lev` is itself the identity. Then the composite `E.lev ≫ p` satisfies, in the exact shape of the level-structure axioms for $(A',f',L',\mathrm{act}')$: it is a closed immersion; the $T$-points of $f'$ factoring through it are closed under $L'$-multiplication and inversion, contain the identity, are killed by $N$ (the $N$-fold $L'$-sum is the identity), and are stable under each $\mathrm{act}'(x)$; the composite of `E.lev ≫ p` with $f'$ is finite, flat and locally of finite presentation, with fibre rank $N^2$ at every point of $\operatorname{Spec} S$; and for every algebraically closed field $k$ and ring homomorphism $S \to k$ with $N \neq 0$ in $k$ there is a bijection from $\mathbb{Z}/N \times \mathbb{Z}/N$ onto the set of $k$-points of $f'$ factoring through `E.lev ≫ p` carrying addition to $L'$-multiplication.
--
--   This is the transport of a level-$N$ structure along a finite homomorphism whose kernel meets the level subscheme trivially, in the style of level structures prime to the degree of an isogeny. It supplies all the level-structure data needed to promote a target $(A',f',L',\mathrm{act}')$ to a fake elliptic curve, and is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLevelIsogeny_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLevelIsogeny_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_levelStructure_lev_comp_of_disjoint.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.levelStructure_lev_comp_of_disjoint
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S)
    {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f') (hc' : L'.IsCommutative)
    (act' : ↥Λ → (A' ⟶ A')) (act'_over : ∀ x : ↥Λ, act' x ≫ f' = f')
    (p : E.A ⟶ A') (hp : p ≫ f' = E.f) [IsFinite p]
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt p hp (E.L.mul t P Q) = L'.mul t (mapPt p hp P) (mapPt p hp Q))
    (hequiv : ∀ x : ↥Λ, E.act x ≫ p = p ≫ act' x)
    (hdisj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt p hp P = L'.one t → FactorsThrough E.lev P → P = E.L.one t) :
    IsClosedImmersion (E.lev ≫ p) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f'),
      FactorsThrough (E.lev ≫ p) P → FactorsThrough (E.lev ≫ p) Q →
        FactorsThrough (E.lev ≫ p) (L'.mul t P Q) ∧ FactorsThrough (E.lev ≫ p) (L'.inv t P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough (E.lev ≫ p) (L'.one t)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f'),
      FactorsThrough (E.lev ≫ p) P → nsmulPt L' t N P = L'.one t) ∧
    (∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f'),
      FactorsThrough (E.lev ≫ p) P → FactorsThrough (E.lev ≫ p) (pushPt (act' x) (act'_over x) P)) ∧
    IsFinite ((E.lev ≫ p) ≫ f') ∧ Flat ((E.lev ≫ p) ≫ f') ∧ LocallyOfFinitePresentation ((E.lev ≫ p) ≫ f') ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ((E.lev ≫ p) ≫ f').finrank s = N ^ 2) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), (N : k) ≠ 0 →
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f' // FactorsThrough (E.lev ≫ p) P},
        ∀ x y : ZMod N × ZMod N, (e (x + y) : SchemeHomOver (geomPoint k sk) f') = L'.mul (geomPoint k sk) (e x) (e y)) := by sorry
