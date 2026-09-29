-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_isNilpotent_ker_of_isNoetherianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_isNilpotent_ker_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/c8c30561-4eab-540c-a421-2fe99e20a0c4
-- title:
--   Lifting rigidifications along nilpotent thickenings
-- statement:
--   Fix a prime $r$ and a nonzero level $N$ with $r \nmid N$, a commutative ring $\mathcal O$ and an element $\pi \in \mathcal O$ generating the same ideal as $r$, and an $\mathcal O$-algebra $O^{\mathrm{nr}}$. Let $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule containing every rational integer, and let $\mathrm{coord} : \Lambda \to \mathrm{Zp2}\,r \times \mathrm{Zp2}\,r$ satisfy `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, is injective, satisfies the twisted multiplicativity rule $(\alpha_1\alpha_2 + r\,\beta_1 F\beta_2,\ \alpha_1\beta_2 + \beta_1 F\alpha_2)$ for Witt-vector Frobenius $F$, has dense image modulo every power of $r$, and matches reduced traces with first coordinates. Let $A_0$ be a fake elliptic curve of level $N$ over $O^{\mathrm{nr}}/\pi$. Let $p : B \to B_0$ be a surjective morphism of $\mathcal O$-algebras with nilpotent kernel, $B$ Noetherian, let $\psi : O^{\mathrm{nr}} \to B$ be an $\mathcal O$-algebra map, and assume $N$ is a unit in $B/\pi$. Let $E$, $E_0$ be fake elliptic curves of level $N$ over $B$ and $B_0$ and $g : E_0.A \to E.A$ a morphism exhibiting $E_0$ as the pullback of $E$ along $p$ (a pullback square of structure maps, compatibility with the relative group law and with the $\Lambda$-action, and lifting of level-structure points), and let $\rho_0$ be a rigidification of $E_0$ relative to $A_0$ and $p \circ \psi$. The conclusion asserts the existence of a rigidification $\rho$ of $E$ relative to $A_0$ and $\psi$, a rigidification $\rho'$ of $E_0$ relative to $A_0$ and $p \circ \psi$, and a witness that $\rho'$ is the pullback of $\rho$ along $p$ (comparison maps $u_b, u_A$ making $\rho'.E_b$, $\rho'.A_b$ pullbacks of $\rho.E_b$, $\rho.A_b$ along $B/\pi \to B_0/\pi$, compatible with the maps to $E$ and to $A_0$, with the same isogeny exponent $d$ and $u_b \circ \rho.\varphi$ matching $u_A \circ \rho'.\varphi$), together with comparison data between $\rho'$ and the given $\rho_0$: a morphism $i_b : \rho_0.E_b.A \to \rho'.E_b.A$ compatible with the maps $\rho_0.g_b$, $\rho'.g_b$ to $E_0.A$ and with the structure maps to $\operatorname{Spec}(B_0/\pi)$, a morphism $u_A : \rho'.A_b.A \to \rho_0.A_b.A$ exhibiting $\rho'.A_b$ as a pullback of $\rho_0.A_b$ along the identity of $B_0/\pi$ and compatible with the maps $\rho_0.g_A$, $\rho'.g_A$ to $A_0$, and natural numbers $i_1, j_1$ with $i_b$ followed by $\rho'.\varphi$, then $u_A$, then the action of $r^{i_1} \in \Lambda$ on $\rho_0.A_b$ equal to $\rho_0.\varphi$ followed by the action of $r^{j_1}$. Thus the lifted rigidification agrees with the given one only up to $r$-power scalars.
--
--   This is the existence half of Drinfeld's rigidity for rigidifications (quasi-isogeny data of fake elliptic curves) along a nilpotent thickening of the base: every rigidification over $B_0$ lifts, up to multiplication by $r$-power scalars, to a rigidification over $B$. It is the deformation-theoretic input used in the construction of rigidified lifts over Artinian bases in the Čerednik–Drinfeld comparison, and is cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedCurve_lift_of_isArtinianRing`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedCurve_lift_of_isArtinianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_isNilpotent_ker_of_isNoetherianRing.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_isNilpotent_ker_of_isNoetherianRing
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (B B₀ : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] [CommRing B₀] [Algebra 𝒪 B₀]
    (p : B →ₐ[𝒪] B₀) (hp : Function.Surjective p) (hpn : IsNilpotent (RingHom.ker (p : B →+* B₀)))
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
