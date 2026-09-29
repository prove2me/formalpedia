-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero_of_isNoetherianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/8ebd62fa-2359-5d0f-a090-522f4538fa14
-- title:
--   Lifting r^mφ₀ across a square-zero thickening
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$, a level $N$ and a prime $r$, together with a map $\mathrm{coord} \colon \Lambda \to \mathbb{W}(\mathbb{F}_{r^2})^2$ satisfying `IsOrderCoord`: it is additive, sends $1$ (when $1 \in \Lambda$) to $(1,0)$, is multiplicative for the twisted rule $(\alpha_1\beta_1 + r\,\alpha_2\varphi(\beta_2),\ \alpha_1\beta_2 + \alpha_2\varphi(\beta_1))$ with $\varphi$ the Witt-vector Frobenius, is injective, has dense image modulo every power of $r$, and matches reduced traces with first coordinates. Let $p \colon S \to S_0$ be a surjective homomorphism of commutative rings with $S$ Noetherian, such that any two elements of $\ker p$ have product zero (so $(\ker p)^2 = 0$), and let $r$ be nilpotent in $S$. Let $E,A$ be fake elliptic curves over $S$ and $E_0,A_0$ fake elliptic curves over $S_0$ — in each case a scheme with structure morphism to the base spectrum, a commutative relative group law, an abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ by endomorphisms over the base that is additive on points and compatible with addition, multiplication and the unit of $\Lambda$ and satisfies the trace condition, plus the level-$N$ data. Let $g \colon E_0 \to E$ and $g_A \colon A_0 \to A$ exhibit $E_0,A_0$ as pull-backs along $p$ in the sense of `FakeEllipticCurve.IsPullbackVia`: each forms a pullback square with the two structure morphisms and $\operatorname{Spec}(p)$, is compatible with the group laws on points and with the $\Lambda$-actions, and carries points factoring through the level structure of the source to points factoring through that of the target. Finally let $\varphi_0 \colon E_0 \to A_0$ be a morphism over $S_0$ which is additive on $T$-points for every $S_0$-scheme $T$ and satisfies $E_0.\mathrm{act}(x)$ followed by $\varphi_0$ equals $\varphi_0$ followed by $A_0.\mathrm{act}(x)$ for all $x \in \Lambda$. Then there exist $m \in \mathbb{N}$ and a morphism $\varphi \colon E \to A$ over $S$ which is additive on $T$-points for every $S$-scheme $T$ and $\Lambda$-equivariant in the same sense, such that for every scheme $T$ over $S_0$ and every $T$-point $P$ of $E_0$ the composite of $P$ with $g$ and then $\varphi$ equals the composite of $g_A$ with the $r^m$-fold multiple, in the group law of $A_0$, of the image of $P$ under $\varphi_0$.
--
--   This is Drinfeld's rigidity statement for homomorphisms of fake elliptic curves along a square-zero thickening of the base on which $r$ is nilpotent: the given homomorphism need not lift, but some $r^m$-multiple of it does, compatibly with the comparison morphisms. It is used in the construction of the Čerednik–Drinfeld rigidification, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_squareZero_of_isNoetherianRing`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_squareZero_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero_of_isNoetherianRing.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero_of_isNoetherianRing
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    {S S₀ : Type} [CommRing S] [IsNoetherianRing S] [CommRing S₀] (p : S →+* S₀)
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
