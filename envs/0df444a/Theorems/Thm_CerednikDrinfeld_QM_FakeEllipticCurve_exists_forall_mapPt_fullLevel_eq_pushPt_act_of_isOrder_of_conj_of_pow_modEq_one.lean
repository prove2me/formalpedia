-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/54864631-918e-5fe9-aa4a-ffae575817dc
-- title:
--   Labelling a conjugated quaternion action on a full level structure
-- statement:
--   Fix naturals $r,N,n$ and an algebraically closed field $k_0$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is an order (contains $1$, is closed under multiplication, spans over $\mathbb{Q}$, and is finitely generated), let $A_0$ be a fake elliptic curve over $k_0$ with $\Lambda$-action of level $N$, and let $P_0$ be a full level-$n$ structure on it: a section of $A_0$ over $\operatorname{Spec} k_0$ killed by $n$ for the relative group law, whose $\Lambda$-orbit exhausts the $n$-torsion at every algebraically closed geometric point, and whose annihilator in $\Lambda$ is exactly $n\Lambda$. Let $R$ be an order in a second algebra $\mathbb{H}[\mathbb{Q},a_1,b_1]$ and $\varepsilon$ a map from $R$ to endomorphisms of the total space of $A_0$ such that each $\varepsilon x$ lies over $\operatorname{Spec} k_0$, is a homomorphism for the group law on points after any base change, is additive in $x$ on points, commutes with the $\Lambda$-action, sends $1$ to the identity, and satisfies $\varepsilon(xy) = \varepsilon y$ followed by $\varepsilon x$. Let $\tilde\Gamma$ be a subgroup of the units of $\mathbb{H}[\mathbb{Q},a_1,b_1]$, $u$ a unit, and $e,K,x$ assignments on $\tilde\Gamma$ with each $e\gamma$ over the base, $x_\gamma = r^{K_\gamma}\cdot u^{-1}\gamma u$ in $R$, $e\gamma = \varepsilon(x_\gamma)$, and $r^{K_\gamma}\equiv 1 \pmod n$. Then there is $\mathrm{lab} : \tilde\Gamma \to \Lambda$ with $(e\gamma)_*P_0 = (\mathrm{lab}\,\gamma)_*P_0$ for all $\gamma$, with $\mathrm{lab}(\gamma\gamma') - \mathrm{lab}(\gamma')\,\mathrm{lab}(\gamma) \in n\Lambda$ for all $\gamma,\gamma'$, and with $\mathrm{lab}(\gamma) - c\cdot 1 \in n\Lambda$ whenever $\gamma$ is the scalar $c\cdot 1$ for an integer $c$.
--
--   This records the passage from a quaternionic action on a fake elliptic curve to its effect on a full level-$n$ structure, encoded as a map $\tilde\Gamma \to \Lambda$ that is anti-multiplicative modulo $n\Lambda$ and agrees with rational integers on rational scalars; this is the bookkeeping underlying level structures in the Čerednik–Drinfel'd description of Shimura curves. It is used in the construction of a fake elliptic curve together with its endomorphism dictionary and formal module structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one
    {r N n : ℕ} (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (A₀ : FakeEllipticCurve Λ N k₀) (P₀ : A₀.FullLevel n)

    {a₁ b₁ : ℚ} (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR : IsOrder R)
    (ε : ↥R → (A₀.A ⟶ A₀.A)) (hε : ∀ x : ↥R, ε x ≫ A₀.f = A₀.f)
    (hε_hom : ∀ (x : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      pushPt (ε x) (hε x) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_lin : ∀ (x : ↥R) (m : ↥Λ), A₀.act m ≫ ε x = ε x ≫ A₀.act m)
    (hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A)
    (hε_mul : ∀ (x y : ↥R) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      ε ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (u : (ℍ[ℚ, a₁, b₁])ˣ)
    (e : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f)
    (K : ↥Γt → ℕ) (x : ↥Γt → ↥R)
    (hx : ∀ γ : ↥Γt, (x γ : ℍ[ℚ, a₁, b₁]) =
      ((r ^ K γ : ℕ) : ℚ) • ((u⁻¹ * (γ : (ℍ[ℚ, a₁, b₁])ˣ) * u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]))
    (he_eq : ∀ γ : ↥Γt, e γ = ε (x γ))
    (hK : ∀ γ : ↥Γt, r ^ K γ ≡ 1 [MOD n]) :
    ∃ lab : ↥Γt → ↥Λ,
      (∀ γ : ↥Γt, mapPt (e γ) (he γ) P₀.P = pushPt (A₀.act (lab γ)) (A₀.act_over (lab γ)) P₀.P) ∧
      (∀ γ γ' : ↥Γt, ∃ y : ↥Λ, (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
          ∃ y : ↥Λ, (lab γ : ℍ[ℚ, a, b]) - (c : ℚ) • (1 : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) := by sorry
