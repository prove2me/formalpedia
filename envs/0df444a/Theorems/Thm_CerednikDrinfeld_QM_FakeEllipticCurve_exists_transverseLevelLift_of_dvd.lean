-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_transverseLevelLift_of_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_transverseLevelLift_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/78a06bea-d64d-5b9a-b00f-05cbc56260ce
-- title:
--   Transverse level-Nℓ lift of the level structure, ℓ ∣ N
-- statement:
--   Let $q,q'$ be primes with $q' \neq q$, let $a,b \in \mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$; let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order: it contains $1$, is closed under multiplication, spans over $\mathbb{Q}$ and is finitely generated; and it is maximal among such), let $N \geq 1$, let $\ell$ be a prime with $\ell \neq q$, $\ell \neq q'$ and $\ell \mid N$, let $k$ be an algebraically closed field in which $\ell$ and $N$ are nonzero, and let $E_0$ be a fake elliptic curve over $k$ of level $N$ with $\Lambda$-action, given by a structure morphism $E_0.f : A \to \operatorname{Spec} k$ with commutative relative group law $E_0.L$, two-dimensional fibres, abelian-scheme property bundle, a $\Lambda$-action $E_0.\mathrm{act}$ over $\operatorname{Spec} k$ compatible with the group law and satisfying the trace condition, and level data including a morphism $E_0.\mathrm{lev}$. Then there exist schemes $\tilde{C}$ and $K_0$ and morphisms $\mathrm{lev}_t : \tilde{C} \to A$, $\mathrm{lev}_K : K_0 \to A$ with the following properties, where a point $P \in \mathrm{SchemeHomOver}\,t\,E_0.f$ (a morphism $T \to A$ over $t : T \to \operatorname{Spec} k$) is said to factor through a morphism $\mathrm{lev}$ when $P$ is a composite $T \to \cdot \to A$ through $\mathrm{lev}$. First, $\mathrm{lev}_t$ is a closed immersion and the composite $\mathrm{lev}_t$ followed by $E_0.f$ is finite, flat and locally of finite presentation; for every $t : T \to \operatorname{Spec} k$ the unit section $E_0.L.\mathrm{one}\,t$ factors through $\mathrm{lev}_t$, the points factoring through $\mathrm{lev}_t$ are closed under $E_0.L.\mathrm{mul}$ and $E_0.L.\mathrm{inv}$ and under $\mathrm{pushPt}$ by $E_0.\mathrm{act}\,x$ for every $x \in \Lambda$; every such point is killed by $N\ell$ for the iterated group law, and $\ell$ times every such point factors through $E_0.\mathrm{lev}$; moreover there is a bijection $\mathbb{Z}/N\ell \times \mathbb{Z}/N\ell \to \{P : \mathrm{SchemeHomOver}\,\mathbf{1}_{\operatorname{Spec} k}\,E_0.f \mid P \text{ factors through } \mathrm{lev}_t\}$ carrying addition to $E_0.L.\mathrm{mul}$. Second, $\mathrm{lev}_K$ is a closed immersion, $\mathrm{lev}_K$ followed by $E_0.f$ is finite, flat and locally of finite presentation with fibre rank $\ell^2$ at every point of $\operatorname{Spec} k$; the points factoring through $\mathrm{lev}_K$ contain the unit section, are closed under the group law, inversion and the $\Lambda$-action, and a point $P$ factors through $\mathrm{lev}_K$ if and only if it factors through $\mathrm{lev}_t$ and $\ell P$ is the unit section.
--
--   This provides, for a prime $\ell$ dividing the level $N$, a lift of the level-$N$ structure on a fake elliptic curve to a $\Lambda$-stable subgroup scheme with group of $k$-points $(\mathbb{Z}/N\ell)^2$ whose $\ell$-multiples land in the given level structure, together with its $\ell$-torsion subscheme of rank $\ell^2$. It is the geometric input for the $\ell \mid N$ case of the surjectivity of the degeneracy map on fake elliptic curves, being used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny_of_dvd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny_of_dvd) and [`CerednikDrinfeld.QM.FakeEllipticCurve.natCard_levelExt_eq_of_dvd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.natCard_levelExt_eq_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_transverseLevelLift_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_transverseLevelLift_of_dvd
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (hℓN : ℓ ∣ N)
    (E₀ : FakeEllipticCurve Λ N k) :
    ∃ (Ct : Scheme.{0}) (levt : Ct ⟶ E₀.A) (K₀ : Scheme.{0}) (levK : K₀ ⟶ E₀.A),
      IsClosedImmersion levt ∧
      IsFinite (levt ≫ E₀.f) ∧
      Flat (levt ≫ E₀.f) ∧
      LocallyOfFinitePresentation (levt ≫ E₀.f) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough levt (E₀.L.one t)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
        FactorsThrough levt P → FactorsThrough levt Q →
          FactorsThrough levt (E₀.L.mul t P Q) ∧ FactorsThrough levt (E₀.L.inv t P)) ∧
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levt P → FactorsThrough levt (pushPt (E₀.act x) (E₀.act_over x) P)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levt P → nsmulPt E₀.L t (N * ℓ) P = E₀.L.one t) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levt P → FactorsThrough E₀.lev (nsmulPt E₀.L t ℓ P)) ∧
      (∃ e : ZMod (N * ℓ) × ZMod (N * ℓ) ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f // FactorsThrough levt P},
        ∀ x y : ZMod (N * ℓ) × ZMod (N * ℓ),
          (e (x + y) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f) = E₀.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y)) ∧
      IsClosedImmersion levK ∧
      IsFinite (levK ≫ E₀.f) ∧
      Flat (levK ≫ E₀.f) ∧
      LocallyOfFinitePresentation (levK ≫ E₀.f) ∧
      (∀ s : ↥(Spec (CommRingCat.of k)), (levK ≫ E₀.f).finrank s = ℓ ^ 2) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough levK (E₀.L.one t)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
        FactorsThrough levK P → FactorsThrough levK Q →
          FactorsThrough levK (E₀.L.mul t P Q) ∧ FactorsThrough levK (E₀.L.inv t P)) ∧
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levK P → FactorsThrough levK (pushPt (E₀.act x) (E₀.act_over x) P)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levK P ↔ (FactorsThrough levt P ∧ nsmulPt E₀.L t ℓ P = E₀.L.one t)) := by sorry
