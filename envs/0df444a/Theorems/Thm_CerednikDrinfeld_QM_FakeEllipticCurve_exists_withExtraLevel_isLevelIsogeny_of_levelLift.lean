-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny_of_levelLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/849a7d0b-4cb0-58fc-9d7a-5fd80f6257d9
-- title:
--   Transverse level lift yields an ℓ-level isogeny onto E₀
-- statement:
--   Fix primes $q \ne q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $q$ or $q'$ lies in $v$; let $\Lambda \subset \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order, maximal among the orders containing it, let $N \ge 1$, let $\ell$ be a prime distinct from $q$ and $q'$, and let $k$ be an algebraically closed field in which $\ell$ and $N$ are nonzero. Let $E_0$ be a fake elliptic curve of level $N$ over $k$ in the sense of the project structure `FakeEllipticCurve` (a scheme $E_0.A$ over $\mathrm{Spec}\,k$ with commutative relative group law $E_0.L$, two-dimensional fibres, abelian-scheme property bundle, $\Lambda$-action $E_0.\mathrm{act}$ and level datum $E_0.\mathrm{lev}$). Assume given two further schemes together with morphisms $\mathrm{levt} : C_t \to E_0.A$ and $\mathrm{levK} : K_0 \to E_0.A$, each a closed immersion whose composite with $E_0.f$ is finite, flat and locally of finite presentation, with these properties, stated in terms of points $P$ over an arbitrary base $t : T \to \mathrm{Spec}\,k$ factoring through the morphism in question: both contain the identity section and are closed under the group law and inversion, and both are stable under all $E_0.\mathrm{act}\,x$, $x \in \Lambda$; every point of $C_t$ is killed by $N\ell$ and its $\ell$-multiple factors through $E_0.\mathrm{lev}$; the $k$-points of $C_t$ (over the identity of $\mathrm{Spec}\,k$) admit an additive bijection from $(\mathbb{Z}/N\ell)^2$; the fibre rank of $K_0$ over every point of $\mathrm{Spec}\,k$ equals $\ell^2$; and a point factors through $\mathrm{levK}$ if and only if it factors through $\mathrm{levt}$ and is killed by $\ell$. The conclusion is that there exists a pair $u = (E,K)$ consisting of a fake elliptic curve $E$ of level $N$ over $k$ and an `ExtraLevel` structure $K$ for $E$ at $\ell$ such that `IsLevelIsogeny ℓ u E₀` holds: there are morphisms $\varphi : E.A \to E_0.A$ and $\psi : E_0.A \to E.A$ over $\mathrm{Spec}\,k$, both additive on points over every base and both commuting with the $\Lambda$-actions, such that whenever $\ell \in \Lambda$ the composites $\varphi$ followed by $\psi$ and $\psi$ followed by $\varphi$ are the actions of $\ell$ on $E.A$ and on $E_0.A$ respectively, a point $P$ of $E$ satisfies $\varphi(P)=0$ precisely when $P$ factors through the extra level $K$, and $\varphi$ carries points factoring through $E.\mathrm{lev}$ to points factoring through $E_0.\mathrm{lev}$.
--
--   This is the construction of the quotient fake elliptic curve with prescribed level: from a level datum $C_t$ lifting $E_0.\mathrm{lev}$ to level $N\ell$ and the $\ell$-torsion subgroup $K_0$ it cuts out, one builds a pair $(E,K)$ whose second degeneracy map $(E,K)\mapsto E/K$ recovers $E_0$. It is the engine behind the surjectivity, on geometric points, of that degeneracy map on the Čerednik–Drinfel'd moduli of fake elliptic curves, and is invoked in the case $\ell \mid N$ by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny_of_dvd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny_of_levelLift
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (E₀ : FakeEllipticCurve Λ N k)
    (Ct : Scheme.{0}) (levt : Ct ⟶ E₀.A) (K₀ : Scheme.{0}) (levK : K₀ ⟶ E₀.A)
    (hCt_closed : IsClosedImmersion levt)
    (hCt_finite : IsFinite (levt ≫ E₀.f))
    (hCt_flat : Flat (levt ≫ E₀.f))
    (hCt_fp : LocallyOfFinitePresentation (levt ≫ E₀.f))
    (hCt_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough levt (E₀.L.one t))
    (hCt_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
        FactorsThrough levt P → FactorsThrough levt Q →
          FactorsThrough levt (E₀.L.mul t P Q) ∧ FactorsThrough levt (E₀.L.inv t P))
    (hCt_stable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levt P → FactorsThrough levt (pushPt (E₀.act x) (E₀.act_over x) P))
    (hCt_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levt P → nsmulPt E₀.L t (N * ℓ) P = E₀.L.one t)
    (hCt_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levt P → FactorsThrough E₀.lev (nsmulPt E₀.L t ℓ P))
    (hCt_points : ∃ e : ZMod (N * ℓ) × ZMod (N * ℓ) ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f // FactorsThrough levt P},
        ∀ x y : ZMod (N * ℓ) × ZMod (N * ℓ),
          (e (x + y) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f) = E₀.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y))
    (hK_closed : IsClosedImmersion levK)
    (hK_finite : IsFinite (levK ≫ E₀.f))
    (hK_flat : Flat (levK ≫ E₀.f))
    (hK_fp : LocallyOfFinitePresentation (levK ≫ E₀.f))
    (hK_rank : ∀ s : ↥(Spec (CommRingCat.of k)), (levK ≫ E₀.f).finrank s = ℓ ^ 2)
    (hK_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough levK (E₀.L.one t))
    (hK_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
        FactorsThrough levK P → FactorsThrough levK Q →
          FactorsThrough levK (E₀.L.mul t P Q) ∧ FactorsThrough levK (E₀.L.inv t P))
    (hK_stable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levK P → FactorsThrough levK (pushPt (E₀.act x) (E₀.act_over x) P))
    (hK_points : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levK P ↔ (FactorsThrough levt P ∧ nsmulPt E₀.L t ℓ P = E₀.L.one t)) :
    ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k, FakeEllipticCurve.IsLevelIsogeny ℓ u E₀ := by sorry
