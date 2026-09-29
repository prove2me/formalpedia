-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/460a573a-47c2-56a8-b01a-24301bf45ded
-- title:
--   Lifting r^mφ₀ along a nilpotent thickening
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a level $N$, and a prime $r$, together with a map $\mathrm{coord}:\Lambda\to \mathbb{W}(\mathbb{F}_{r^2})^2$ satisfying `IsOrderCoord`: it is additive and injective, sends $1$ (when $1\in\Lambda$) to $(1,0)$, is multiplicative for the twisted rule $(\alpha_1\alpha_2+r\,\beta_1\varphi(\beta_2),\ \alpha_1\beta_2+\beta_1\varphi(\alpha_2))$ with $\varphi$ the Witt-vector Frobenius, has image dense modulo every power of $r$, and matches reduced traces. Let $p:S\to S_0$ be a surjective homomorphism of commutative rings whose kernel is a nilpotent ideal, and suppose $r$ is nilpotent in $S$. Let $E,A$ be fake elliptic curves over $S$ and $E_0,A_0$ over $S_0$, and let $g:E_0\to E$, $g_A:A_0\to A$ exhibit the latter as pull-backs along $p$ in the sense of `FakeEllipticCurve.IsPullbackVia`: each square is a pullback over $\operatorname{Spec}p$, each comparison map respects the relative group laws and the $\Lambda$-actions, and carries points factoring through the level structure of the source to points factoring through that of the target. Let $\varphi_0:E_0\to A_0$ be a morphism over $S_0$ which is additive for the relative group laws on points and satisfies $E_0.\mathrm{act}(x)$ followed by $\varphi_0$ equals $\varphi_0$ followed by $A_0.\mathrm{act}(x)$ for all $x\in\Lambda$. Then there are $m\in\mathbb{N}$ and a morphism $\varphi:E\to A$ over $S$, again additive on points and $\Lambda$-equivariant, such that for every scheme $T$ over $S_0$ and every $T$-point $P$ of $E_0$, the composite of $P$ with $g$ and then $\varphi$ equals the composite of the $r^m$-th multiple of $\varphi_0\circ P$ in the group law of $A_0$ with $g_A$.
--
--   This is the rigidity statement that a homomorphism of fake elliptic curves over $S_0$ lifts, after multiplication by a power of $r$, across a thickening $S\to S_0$ with nilpotent kernel on which $r$ is nilpotent — the form of Drinfeld's rigidity for quasi-isogenies used in the Čerednik–Drinfeld uniformisation, obtained by the usual trick of killing the obstruction by a power of $r$. It is used in the construction of pull-back compatible rigidifications, [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_isNilpotent_ker_of_isNoetherianRing`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_isNilpotent_ker_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    {S S₀ : Type} [CommRing S] [CommRing S₀] (p : S →+* S₀)
    (hp : Function.Surjective p) (hpn : IsNilpotent (RingHom.ker p)) (hr : IsNilpotent ((r : ℕ) : S))

    (E A : FakeEllipticCurve Λ N S) (E₀ A₀ : FakeEllipticCurve Λ N S₀)
    (g : E₀.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia p E E₀ g)
    (gA : A₀.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia p A A₀ gA)

    (φ₀ : E₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = E₀.f)
    (φ₀_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t E₀.f),
      mapPt φ₀ hφ₀ (E₀.L.mul t P Q) = A₀.L.mul t (mapPt φ₀ hφ₀ P) (mapPt φ₀ hφ₀ Q))
    (φ₀_act : ∀ x : ↥Λ, E₀.act x ≫ φ₀ = φ₀ ≫ A₀.act x) :
    ∃ (m : ℕ) (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
        mapPt φ hφ (E.L.mul t P Q) = A.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ A.act x) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t E₀.f),
        P.1 ≫ g ≫ φ = (nsmulPt A₀.L t (r ^ m) (mapPt φ₀ hφ₀ P)).1 ≫ gA) := by sorry
