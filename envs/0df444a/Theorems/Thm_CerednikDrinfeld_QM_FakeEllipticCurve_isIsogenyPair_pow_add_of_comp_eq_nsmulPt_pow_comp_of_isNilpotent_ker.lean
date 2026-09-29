-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isIsogenyPair_pow_add_of_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isIsogenyPair_pow_add_of_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/a86c0947-e333-56a0-a4db-eddf6de751f8
-- title:
--   Isogeny pairs lift along nilpotent thickenings
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ containing the image of every integer (hypothesis `hΛℤ`), a natural number $N$ and a prime $r$. Let $p : S \to S_0$ be a surjective homomorphism of commutative rings whose kernel is a nilpotent ideal. Let $E,A$ be fake elliptic curves for $(\Lambda,N)$ over $S$ and $E_0,A_0$ such objects over $S_0$, together with morphisms $g : E_0.A \to E.A$ and $g_A : A_0.A \to A.A$ exhibiting $E_0,A_0$ as base changes along $p$ in the sense of `IsPullbackVia`: each square over $\mathrm{Spec}$ of $p$ is a pullback, $g$ and $g_A$ carry relative group-law products to products, commute with the $\Lambda$-actions, and send points factoring through the level structure to points factoring through it. Let $\varphi : E.A \to A.A$ and $\varphi' : A.A \to E.A$ be morphisms over $S$ (hypotheses $h\varphi$, $h\varphi'$) which are additive for the relative group laws on functorially parametrised points and commute with the $\Lambda$-actions. Let $\varphi_0 : E_0.A \to A_0.A$ and $\varphi_0' : A_0.A \to E_0.A$ be morphisms over $S_0$, and let $d,m,m'$ be natural numbers such that $(\varphi_0,\varphi_0')$ is an isogeny pair of degree $r^d$, i.e. both are additive, $\Lambda$-equivariant and, whenever $r^d$ lies in $\Lambda$, $\varphi_0$ followed by $\varphi_0'$ is the action of $r^d$ on $E_0$ and $\varphi_0'$ followed by $\varphi_0$ is the action of $r^d$ on $A_0$. Assume finally that for every $S_0$-scheme $T \to \mathrm{Spec}\,S_0$ and every point $P$ of $E_0$ over it, $P$ followed by $g$ and $\varphi$ equals the $r^m$-fold multiple (iterated relative group law, `nsmulPt`) of $\varphi_0 \circ P$ followed by $g_A$, and symmetrically that for every point $Q$ of $A_0$, $Q$ followed by $g_A$ and $\varphi'$ equals the $r^{m'}$-fold multiple of $\varphi_0' \circ Q$ followed by $g$. Then $(\varphi,\varphi')$ is an isogeny pair of degree $r^{d+m+m'}$ for $E$ and $A$: both are additive and $\Lambda$-equivariant over $S$, and (the membership being guaranteed by `hΛℤ`) $\varphi$ followed by $\varphi'$ is the action of $r^{d+m+m'}$ on $E$ while $\varphi'$ followed by $\varphi$ is its action on $A$.
--
--   This is the rigidity step for homomorphisms of abelian schemes along a nilpotent thickening, in the form needed for fake elliptic curves with quaternionic multiplication: a pair of morphisms over $S$ whose reductions are $r^m\varphi_0$ and $r^{m'}\varphi_0'$ for an isogeny pair of degree $r^d$ is itself an isogeny pair, of degree $r^{d+m+m'}$. It is used in the construction of rigidifications lifting along surjections with nilpotent (in particular square-zero) kernel, by the three results `exists_isPullbackVia_corr_of_isNilpotent_ker_of_isNoetherianRing`, `exists_isPullbackVia_corr_of_squareZero` and `exists_isPullbackVia_corr_of_squareZero_of_isNoetherianRing`; the proof appeals to [`GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker`](thm.html#GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isIsogenyPair_pow_add_of_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isIsogenyPair_pow_add_of_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {r : ℕ} [Fact r.Prime]

    {S S₀ : Type} [CommRing S] [CommRing S₀] (p : S →+* S₀)
    (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (E A : FakeEllipticCurve Λ N S) (E₀ A₀ : FakeEllipticCurve Λ N S₀)
    (g : E₀.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia p E E₀ g)
    (gA : A₀.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia p A A₀ gA)

    (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f) (φ' : A.A ⟶ E.A) (hφ' : φ' ≫ E.f = A.f)
    (φ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = A.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (φ'_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
      mapPt φ' hφ' (A.L.mul t P Q) = E.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q))
    (φ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ A.act x) (φ'_act : ∀ x : ↥Λ, A.act x ≫ φ' = φ' ≫ E.act x)

    (φ₀ : E₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = E₀.f) (φ₀' : A₀.A ⟶ E₀.A) (hφ₀' : φ₀' ≫ E₀.f = A₀.f) (d m m' : ℕ)
    (h₀ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E₀ A₀ φ₀ φ₀')
    (hred : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t E₀.f),
      P.1 ≫ g ≫ φ = (nsmulPt A₀.L t (r ^ m) (mapPt φ₀ hφ₀ P)).1 ≫ gA)
    (hred' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (Q : SchemeHomOver t A₀.f),
      Q.1 ≫ gA ≫ φ' = (nsmulPt E₀.L t (r ^ m') (mapPt φ₀' hφ₀' Q)).1 ≫ g) :
    FakeEllipticCurve.IsIsogenyPair (r ^ (d + m + m')) E A φ φ' := by sorry
