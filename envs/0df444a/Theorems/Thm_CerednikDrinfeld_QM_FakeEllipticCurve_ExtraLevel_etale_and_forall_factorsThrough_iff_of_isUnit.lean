-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/44c4178b-073c-5b28-a414-f191f73110e4
-- title:
--   Étale extra level at invertible ℓ and its geometric points
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, a commutative ring $S$, and a fake elliptic curve $E$ of type $(\Lambda,N)$ over $S$, so in particular $E$ carries a scheme $E.A$ with structure morphism $E.f : E.A \to \operatorname{Spec} S$ and a commutative relative group law $E.L$ on $E.f$. Let $\ell$ be a natural number whose image in $S$ is a unit, and let $K$ be an extra level at $\ell$ on $E$: thus $K$ consists of a scheme with a closed immersion $K.\mathrm{levK} : K \to E.A$ whose functor of points is closed under the group law, contains the unit section, is killed by $\ell$, is stable under the $\Lambda$-action and meets $E.\mathrm{lev}$ only in the unit, together with finiteness, flatness and finite presentation of $K.\mathrm{levK} \circ$ followed by $E.f$, fibre rank $\ell^2$, and geometric fibres isomorphic as groups to $\mathbb Z/\ell \times \mathbb Z/\ell$. Then first, the composite $K.\mathrm{levK}$ followed by $E.f$ is étale; and second, for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every $T$-point $P$ of $E.A$ over $t$ (a morphism $T \to E.A$ whose composite with $E.f$ is $t$), $P$ factors through $K.\mathrm{levK}$ (i.e.\ $P$ is $P_0$ followed by $K.\mathrm{levK}$ for some $P_0 : T \to K$) if and only if the $\ell$-fold sum of $P$ for $E.L$ equals the unit section at $t$ and, for every algebraically closed field $k$, every ring homomorphism $sk : S \to k$ and every $\tau : \operatorname{Spec} k \to T$ whose composite with $t$ is $\operatorname{Spec}(sk)$, the point $\tau$ followed by $P$ factors through $K.\mathrm{levK}$.
--
--   This is the étaleness of an extra level structure at an integer invertible on the base, together with the resulting criterion exhibiting it as the subfunctor of $\ell$-torsion points cut out by a condition on geometric points; it rests on the étaleness of the $\ell$-torsion subscheme of a fake elliptic curve. It is used in the subsequent identification of extra levels with their geometric points and in the comparison of extra levels with period maps in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open NeronModelInfra hiding schemeHomOverComp
open GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℕ) : S)) (K : E.ExtraLevel ℓ) :
    Etale (K.levK ≫ E.f) ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough K.levK P ↔
        nsmulPt E.L t ℓ P = E.L.one t ∧
        ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (τ : Spec (CommRingCat.of k) ⟶ T)
          (hτ : τ ≫ t = geomPoint k sk), FactorsThrough K.levK (schemeHomOverComp τ hτ P) := by sorry
