-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_equiv_of_equiv_of_isPullbackVia_of_ker_sq_eq_bot
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.equiv_of_equiv_of_isPullbackVia_of_ker_sq_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/a6f4a9a6-ae4b-569f-92e1-bcde37b23959
-- title:
--   Equivalence of rigidifications descends along square-zero surjections
-- statement:
--   Fix a prime $r$ and a nonzero $N$ with $r \nmid N$, a commutative ring $\mathcal{O}$ and an element $\pi \in \mathcal{O}$ generating the same ideal as $r$, a commutative $\mathcal{O}$-algebra $O^{\mathrm{nr}}$, rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ containing every rational integer (hypothesis $h\Lambda\mathbb{Z}$), together with a fake elliptic curve $A_0$ with $\Lambda$-action and level-$N$ data over $O^{\mathrm{nr}}/(\pi)$. Let $p : B \to B_0$ be a surjection of $\mathcal{O}$-algebras whose kernel squares to zero, let $\psi : O^{\mathrm{nr}} \to B$ be an $\mathcal{O}$-algebra map, and let $E$ over $B$, $E_0$ over $B_0$ be fake elliptic curves with a morphism $g : E_0.A \to E.A$ exhibiting $E_0$ as the pullback of $E$ along $p$, that is: the square formed by $g$, the structure maps and $\mathrm{Spec}\,p$ is cartesian, $g$ carries the relative group law of $E_0$ on $T$-points to that of $E$, it intertwines the $\Lambda$-actions, and every point of $E_0$ factoring through its level scheme has image under $g$ factoring through that of $E$. Given rigidifications $\rho,\rho'$ of $E$ (relative to $r$, $\pi$, $A_0$, $\psi$) and $\rho_0,\rho_0'$ of $E_0$ (relative to $p \circ \psi$) such that $\rho_0$ is the pullback of $\rho$ and $\rho_0'$ that of $\rho'$ along $(p,g)$ — meaning there are morphisms $u_b, u_A$ over the induced map $B/(\pi) \to B_0/(\pi)$ exhibiting the reduced curve and the auxiliary curve downstairs as pullbacks, compatible with the comparison maps $g_b$, $g_A$ and with $\varphi$, and with equal isogeny exponents $d$ — the conclusion is: if $\rho_0$ and $\rho_0'$ are equivalent, i.e. there are $u$, $u_A$ satisfying `IsComparison` and natural numbers $i,j$ with $u \circ \varphi$ twisted by $r^i$ equal to $\varphi$ then $u_A$ twisted by $r^j$, then $\rho$ and $\rho'$ are equivalent in the same sense.
--
--   This is the rigidity (infinitesimal uniqueness) step for rigidifications of fake elliptic curves: an equivalence of rigidifications over a square-zero quotient of the base already forces equivalence over the base itself. It is used by the lifting statement [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot), in the construction of the Čerednik–Drinfel'd style formal moduli description.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_equiv_of_equiv_of_isPullbackVia_of_ker_sq_eq_bot.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.equiv_of_equiv_of_isPullbackVia_of_ker_sq_eq_bot
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (B B₀ : Type) [CommRing B] [Algebra 𝒪 B] [CommRing B₀] [Algebra 𝒪 B₀]
    (p : B →ₐ[𝒪] B₀) (hp : Function.Surjective p) (hp2 : RingHom.ker (p : B →+* B₀) ^ 2 = ⊥)
    (ψ : Onr →ₐ[𝒪] B)

    (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) E E₀ g)
    (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ρ₀ ρ₀' : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀)
    (h : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ρ ρ₀)
    (h' : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ρ' ρ₀')
    (he : FakeEllipticCurve.Rigidification.Equiv hΛℤ ρ₀ ρ₀') :
    FakeEllipticCurve.Rigidification.Equiv hΛℤ ρ ρ' := by sorry
