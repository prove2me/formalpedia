-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/10548e33-ee82-57fc-a193-6f0380d0b619
-- title:
--   Lifting r^m-multiples of homomorphisms along square-zero thickenings
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a level $N$ and a prime $r$, together with a map $\mathrm{coord}:\Lambda\to \mathrm{Zp2}\,r\times \mathrm{Zp2}\,r$ satisfying `IsOrderCoord`: it is additive, sends $1$ (when $1\in\Lambda$) to $(1,0)$, is multiplicative for the twisted rule $(\alpha_1\beta_1+r\,\alpha_2\varphi(\beta_2),\ \alpha_1\beta_2+\alpha_2\varphi(\beta_1))$ with $\varphi$ the Witt-vector Frobenius, is injective, has dense image modulo every power of $r$, and matches reduced traces. Let $p:S\to S_0$ be a surjective ring homomorphism whose kernel has square zero (any two elements killed by $p$ have product $0$), with $r$ nilpotent in $S$. Let $E,A$ be fake elliptic curves of type $(\Lambda,N)$ over $S$ and $E_0,A_0$ over $S_0$ — abelian schemes with commutative relative group law, two-dimensional fibres, $\Lambda$-action and level data — and let $g:E_0\to E$, $g_A:A_0\to A$ exhibit $E_0,A_0$ as the base changes of $E,A$ along $p$ in the sense of `FakeEllipticCurve.IsPullbackVia` (pullback square of structure maps, compatibility with the group laws, $\Lambda$-equivariance, and descent of points factoring through the level scheme). Let $\varphi_0:E_0\to A_0$ be a morphism over $S_0$ which is additive on $T$-points and $\Lambda$-equivariant. Then there exist $m\in\mathbb{N}$ and a morphism $\varphi:E\to A$ over $S$, additive on $T$-points for every scheme $T$ over $S$ and satisfying $E.\mathrm{act}\,x$ followed by $\varphi$ equals $\varphi$ followed by $A.\mathrm{act}\,x$ for all $x\in\Lambda$, such that for every scheme $T$ over $S_0$ and every $T$-point $P$ of $E_0$ the composite $P$ followed by $g$ followed by $\varphi$ equals the $r^m$-fold multiple of $\varphi_0\circ P$ in the group law of $A_0$, followed by $g_A$.
--
--   This is the rigidity-and-lifting step for homomorphisms of fake elliptic curves: along a square-zero thickening on which the prime $r$ is nilpotent, some $r^m$-multiple of a given $\Lambda$-linear homomorphism downstairs extends to a $\Lambda$-linear homomorphism upstairs. It is used in the construction of rigidifications over square-zero thickenings, in the Cherednik–Drinfeld uniformisation of Shimura curves attached to an indefinite rational quaternion algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    {S S₀ : Type} [CommRing S] [CommRing S₀] (p : S →+* S₀)
    (hp : Function.Surjective p) (hp2 : ∀ s t : S, p s = 0 → p t = 0 → s * t = 0) (hr : IsNilpotent ((r : ℕ) : S))

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
