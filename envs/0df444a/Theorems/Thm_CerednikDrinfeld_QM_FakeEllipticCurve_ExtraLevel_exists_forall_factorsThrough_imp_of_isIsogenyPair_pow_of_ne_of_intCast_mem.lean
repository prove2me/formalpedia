-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/0d978b58-2c18-5d1d-b64d-39fb21dabfc3
-- title:
--   Extra level at ℓ transports uniquely along an isogeny
-- statement:
--   Let $a,b\in\mathbb Q$, let $\Lambda$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,a,b]$ containing the image of every integer, let $N$ be a natural number and $S$ a commutative ring. Let $E,E'$ be fake elliptic curves over $S$ with $\Lambda$-action and level $N$ in the sense of `FakeEllipticCurve`, let $r$ be a prime, $d$ a natural number, $\varphi:E.A\to E'.A$ a morphism with $\varphi$ followed by $E'.f$ equal to $E.f$, and $\psi:E'.A\to E.A$, such that $(\varphi,\psi)$ is an isogeny pair of degree $r^{d}$: both are morphisms over $\operatorname{Spec}S$, both are additive on $T$-points for the relative group laws, both commute with the $\Lambda$-actions, and whenever $r^{d}$ lies in $\Lambda$ the composites $\varphi\psi$ and $\psi\varphi$ are the actions of $r^{d}$ on $E$ and on $E'$. Assume moreover that $\varphi$ preserves the level-$N$ structure, i.e. any $T$-point of $E$ factoring through $E.\mathrm{lev}$ is carried by $\varphi$ to a point factoring through $E'.\mathrm{lev}$. Let $\ell$ be a prime with $\ell\neq r$ and $\ell$ invertible in $S$, and let $K'$ be an extra level at $\ell$ on $E'$ (a closed immersion $K'.\mathrm{levK}\to E'.A$ whose points form a $\Lambda$-stable subgroup of $\ell$-torsion points, disjoint from the level-$N$ structure, finite flat of finite presentation of fibre rank $\ell^{2}$, with geometric fibres $(\mathbb Z/\ell)^{2}$). Then there is an extra level $K$ at $\ell$ on $E$ such that every $T$-point of $E$ (over any $t:T\to\operatorname{Spec}S$) factoring through $K.\mathrm{levK}$ is sent by $\varphi$ to a point factoring through $K'.\mathrm{levK}$, and such that any extra level $K_2$ at $\ell$ on $E$ with this same property has exactly the same points as $K$: for all $t$ and all $P$, $P$ factors through $K.\mathrm{levK}$ if and only if it factors through $K_2.\mathrm{levK}$.
--
--   This is the transport of auxiliary $\ell$-level structures along an isogeny of degree prime to $\ell$: since $\ell\neq r$ and $\ell$ is invertible in $S$, multiplication by $r^{d}$ is invertible on $\ell$-torsion, so $\varphi$ identifies the $\ell$-torsion of $E$ with that of $E'$ and $K'$ pulls back to an extra level on $E$, determined by its points. It is used in the rigidification step for fake elliptic curves with extra level, where extra levels on isogenous curves must be matched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {N : ℕ}
    {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (r d : ℕ) [Fact r.Prime] (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A)
    (hiso : FakeEllipticCurve.IsIsogenyPair (r ^ d) E E' φ ψ) (hlev : FakeEllipticCurve.PreservesLevel E E' φ hφ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓr : ℓ ≠ r) (hℓ : IsUnit ((ℓ : ℕ) : S))
    (K' : E'.ExtraLevel ℓ) :
    ∃ K : E.ExtraLevel ℓ,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough K.levK P → FactorsThrough K'.levK (mapPt φ hφ P)) ∧
      ∀ K₂ : E.ExtraLevel ℓ,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
            FactorsThrough K₂.levK P → FactorsThrough K'.levK (mapPt φ hφ P)) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough K.levK P ↔ FactorsThrough K₂.levK P := by sorry
