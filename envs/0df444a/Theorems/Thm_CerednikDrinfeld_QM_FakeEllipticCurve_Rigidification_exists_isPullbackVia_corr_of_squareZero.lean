-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_squareZero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_squareZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/962eb647-8218-56d0-9a88-f5f4f8e1f4dc
-- title:
--   Lifting rigidifications along square-zero thickenings, up to r-power scalars
-- statement:
--   Fix a prime $r$ and a nonzero natural number $N$ with $r \nmid N$, a commutative ring $\mathcal O$ and an element $\pi \in \mathcal O$ with $(r) = (\pi)$, and an $\mathcal O$-algebra $O^{\mathrm{nr}}$. Let $\Lambda$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,a,b]$ containing every rational integer, equipped with a map $\mathrm{coord} : \Lambda \to W(\mathbb F_{r^2})^2$ satisfying `IsOrderCoord`: additive, sending $1$ to $(1,0)$, multiplicative for the twisted rule involving $r$ and Witt-vector Frobenius, injective, with dense image in the $r$-adic sense, and compatible with reduced traces. Let $A_0$ be a fake elliptic curve of level $N$ over $O^{\mathrm{nr}}/\pi$. Let $p : B \to B_0$ be a surjective map of $\mathcal O$-algebras whose kernel is square zero (any two elements annihilated by $p$ have product $0$), let $\psi : O^{\mathrm{nr}} \to B$ be an $\mathcal O$-algebra map, and assume $N$ is a unit in $B/\pi$. Let $E$, $E_0$ be fake elliptic curves of level $N$ over $B$, $B_0$ and $g : E_0.A \to E.A$ a morphism exhibiting $E_0$ as the base change of $E$ along $p$ in the sense of `FakeEllipticCurve.IsPullbackVia` (cartesian square of structure morphisms, compatibility with the relative group law and the $\Lambda$-action, and descent of level points). Let $\rho_0$ be a rigidification of $E_0$ relative to $(A_0, p \circ \psi)$, that is: the $\pi$-reduction $E_{0,b}$ of $E_0$ over $B_0/\pi$ with its comparison morphism, the base change $A_{0,b}$ of $A_0$ along $O^{\mathrm{nr}}/\pi \to B_0/\pi$, an integer $d$, and a level-preserving pair $\varphi, \varphi'$ of $\Lambda$-equivariant isogenies between $E_{0,b}$ and $A_{0,b}$ of degree $r^{d}$. The conclusion asserts the existence of a rigidification $\rho$ of $E$ relative to $(A_0,\psi)$ and a rigidification $\rho'$ of $E_0$ relative to $(A_0, p\circ\psi)$ with $\rho'$ a pull-back of $\rho$ along $p$ in the sense of `FakeEllipticCurve.Rigidification.IsPullbackVia` (comparison morphisms on the $E_b$- and $A_b$-parts that are cartesian over $B/\pi \to B_0/\pi$, compatible with $gb$ and $gA$, equal degrees, and intertwining the two $\varphi$'s), together with a morphism $ib : \rho_0.Eb.A \to \rho'.Eb.A$ such that $ib$ followed by $\rho'.gb$ equals $\rho_0.gb$ followed by the identity of $E_0.A$ and $ib$ followed by $\rho'.Eb.f$ equals $\rho_0.Eb.f$, a morphism $uA : \rho'.Ab.A \to \rho_0.Ab.A$ exhibiting $\rho_0.Ab$ as a pull-back of $\rho'.Ab$ along the identity of $B_0/\pi$ and satisfying $uA$ followed by $\rho_0.gA$ equals $\rho'.gA$, and natural numbers $i_1, j_1$ with $ib$ followed by $\rho'.\varphi$, then $uA$, then the action of $r^{i_1} \in \Lambda$ on $\rho_0.Ab$ equal to $\rho_0.\varphi$ followed by the action of $r^{j_1}$.
--
--   This is the existence (surjectivity) half of Drinfeld's rigidity statement for rigidified fake elliptic curves: a rigidification of the reduction $E_0$ of $E$ along a square-zero thickening lifts to $E$, uniquely only after composing with powers of $r$. It is used in the proof of [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot), in establishing the infinitesimal lifting property of the functor of rigidified fake elliptic curves underlying the Čerednik–Drinfeld comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_squareZero.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_squareZero
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (B B₀ : Type) [CommRing B] [Algebra 𝒪 B] [CommRing B₀] [Algebra 𝒪 B₀]
    (p : B →ₐ[𝒪] B₀) (hp : Function.Surjective p) (hp2 : ∀ s t : B, p s = 0 → p t = 0 → s * t = 0)
    (ψ : Onr →ₐ[𝒪] B) (hNb : IsUnit ((N : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))

    (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) E E₀ g)
    (ρ₀ : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀) :
    ∃ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀)
      (_ : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ρ ρ'),
      ∃ (ib : ρ₀.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ₀.gb ≫ (Iso.refl E₀.A).hom) (_ : ib ≫ ρ'.Eb.f = ρ₀.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₀.Ab ρ'.Ab uA) (_ : uA ≫ ρ₀.gA = ρ'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ρ'.φ ≫ uA ≫ ρ₀.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₀.φ ≫ ρ₀.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
