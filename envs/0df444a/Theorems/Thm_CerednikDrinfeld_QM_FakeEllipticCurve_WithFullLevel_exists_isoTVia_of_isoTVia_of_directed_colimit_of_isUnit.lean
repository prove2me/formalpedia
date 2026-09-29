-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isoTVia_of_isoTVia_of_directed_colimit_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isoTVia_of_isoTVia_of_directed_colimit_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/aa562f82-6bfa-5eef-98ba-5dc5ed8c234f
-- title:
--   Descent of triple isomorphisms along a directed colimit
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'` (that is, $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $q \in v$ or $q' \in v$), a $\mathbb{Z}$-submodule $\Lambda$ that is a maximal order, a nonzero $N$, an $m \ge 3$, and an $\ell$. Let $(S_i)_{i \in \iota}$ be a directed system of commutative rings over a nonempty directed preorder, with transition maps $t_{ij}$ satisfying $t_{ii} = \mathrm{id}$ and $t_{jk} \circ t_{ij} = t_{ik}$, and let $L$ be a commutative ring with maps $c_i : S_i \to L$ satisfying $c_j \circ t_{ij} = c_i$, jointly surjective, and such that $c_i y = c_i z$ implies $t_{ij} y = t_{ij} z$ for some $j \ge i$; assume $N$, $m$ and $\ell$ are units in $L$. The assertion is: for every index $i$, every pair $v, w$ of fake elliptic curves over $S_i$ with $\Lambda$-action, level-$N$ datum and full level-$m$ structure, every $\ell$-level structures $C_v, C_w$ on them, every $v', w'$ over $L$ with $\ell$-level structures $C_{v'}, C_{w'}$, and morphisms $g_v : v'.A \to v.A$, $g_w : w'.A \to w.A$ for which: $g_v$ makes $v'$ a base change of $v$ along $c_i$ in the sense of `IsPullbackVia` (pullback square, compatibility with the relative group law, commutation with the $\Lambda$-action, and points factoring through $v'.\mathrm{lev}$ mapping into $v.C$), the full-level section satisfies $(v'.P) \circ g_v = (v.P) \circ \operatorname{Spec}(c_i)$ in diagrammatic order, and every $T$-point of $v'$ over $\operatorname{Spec} L$ factoring through $C_{v'}.\mathrm{levK}$ becomes, after composing with $g_v$, a point factoring through $C_v.\mathrm{levK}$; and likewise for $w, g_w$: if $v'$ and $w'$ are isomorphic as triples over $L$, i.e. there is an isomorphism $e : v'.A \cong w'.A$ over $\operatorname{Spec} L$ with `IsoTVia` (compatibility with the group laws and the $\Lambda$-action, equivalence of factorisation through the $\mathrm{lev}$-subschemes, matching of the full-level sections, and equivalence of factorisation through $C_{v'}.\mathrm{levK}$ and $C_{w'}.\mathrm{levK}$), then there are $j \ge i$, objects $v_j, w_j$ over $S_j$ with $\ell$-level structures $C_{v_j}, C_{w_j}$ and morphisms $g_{v_j}, g_{w_j}$ satisfying the same three conditions relative to $t_{ij}$, together with an isomorphism $v_j.A \cong w_j.A$ over $\operatorname{Spec} S_j$ satisfying `IsoTVia` for $v_j, w_j, C_{v_j}, C_{w_j}$.
--
--   This is the descent-of-isomorphisms half of the statement that the moduli problem for triples (fake elliptic curve with level-$N$ datum, full level-$m$ structure, extra $\ell$-level structure) commutes with directed colimits of rings: an isomorphism over the colimit $L$ already exists over some finite stage $S_j$, after replacing the given objects by base changes along $t_{ij}$. It is used in establishing [`CerednikDrinfeld.QM.IsFineModuliT.locallyOfFinitePresentation`](thm.html#CerednikDrinfeld.QM.IsFineModuliT.locallyOfFinitePresentation), the local finite presentation of the corresponding fine moduli scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isoTVia_of_isoTVia_of_directed_colimit_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isoTVia_of_isoTVia_of_directed_colimit_of_isUnit
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (m : ℕ) (hm : 3 ≤ m) (ℓ : ℕ)
    (ι : Type) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Type) [∀ i, CommRing (S i)]
    (t : ∀ i j, i ≤ j → (S i →+* S j))
    (ht₁ : ∀ i (h : i ≤ i), t i i h = RingHom.id (S i))
    (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
    (L : Type) [CommRing L] (c : ∀ i, S i →+* L)
    (hc : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
    (hcsurj : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
    (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z)
    (hNL : IsUnit ((N : ℕ) : L)) (hmL : IsUnit ((m : ℕ) : L)) (hℓL : IsUnit ((ℓ : ℕ) : L)) :
    (∀ (i : ι) (v w : FakeEllipticCurve.WithFullLevel Λ N m (S i)) (Cv : v.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ)
        (v' w' : FakeEllipticCurve.WithFullLevel Λ N m L) (Cv' : v'.1.ExtraLevel ℓ) (Cw' : w'.1.ExtraLevel ℓ)
        (gv : v'.1.A ⟶ v.1.A) (gw : w'.1.A ⟶ w.1.A),
        FakeEllipticCurve.IsPullbackVia (c i) v.1 v'.1 gv →
        (v'.2.P).1 ≫ gv = Spec.map (CommRingCat.ofHom (c i)) ≫ (v.2.P).1 →
        (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' v'.1.f),
          FactorsThrough Cv'.levK P → ∃ P₀ : T ⟶ Cv.K, P₀ ≫ Cv.levK = P.1 ≫ gv) →
        FakeEllipticCurve.IsPullbackVia (c i) w.1 w'.1 gw →
        (w'.2.P).1 ≫ gw = Spec.map (CommRingCat.ofHom (c i)) ≫ (w.2.P).1 →
        (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' w'.1.f),
          FactorsThrough Cw'.levK P → ∃ P₀ : T ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ gw) →
        (∃ (e : v'.1.A ≅ w'.1.A) (he : e.hom ≫ w'.1.f = v'.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia v' w' Cv' Cw' e he) →
        ∃ (j : ι) (h : i ≤ j) (vj wj : FakeEllipticCurve.WithFullLevel Λ N m (S j))
          (Cvj : vj.1.ExtraLevel ℓ) (Cwj : wj.1.ExtraLevel ℓ) (gvj : vj.1.A ⟶ v.1.A) (gwj : wj.1.A ⟶ w.1.A),
          FakeEllipticCurve.IsPullbackVia (t i j h) v.1 vj.1 gvj ∧
          (vj.2.P).1 ≫ gvj = Spec.map (CommRingCat.ofHom (t i j h)) ≫ (v.2.P).1 ∧
          (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (S j))) (P : SchemeHomOver t' vj.1.f),
            FactorsThrough Cvj.levK P → ∃ P₀ : T ⟶ Cv.K, P₀ ≫ Cv.levK = P.1 ≫ gvj) ∧
          FakeEllipticCurve.IsPullbackVia (t i j h) w.1 wj.1 gwj ∧
          (wj.2.P).1 ≫ gwj = Spec.map (CommRingCat.ofHom (t i j h)) ≫ (w.2.P).1 ∧
          (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (S j))) (P : SchemeHomOver t' wj.1.f),
            FactorsThrough Cwj.levK P → ∃ P₀ : T ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ gwj) ∧
          ∃ (e : vj.1.A ≅ wj.1.A) (he : e.hom ≫ wj.1.f = vj.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia vj wj Cvj Cwj e he) := by sorry
