-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/c4975764-ed06-5a54-b2e3-ecf800ac1c9d
-- title:
--   Rigidifications pull back along maps of coefficient algebras
-- statement:
--   Fix natural numbers $r, N$, a commutative ring $\mathcal{O}$ with an element $\pi$, a commutative ring $O^{\mathrm{nr}}$ that is an $\mathcal{O}$-algebra, rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, together with a fake elliptic curve $A_0$ for $\Lambda$ of level $N$ over $O^{\mathrm{nr}}/(\pi)$. Let $B, B'$ be commutative $\mathcal{O}$-algebras, $\varphi : B \to B'$ an $\mathcal{O}$-algebra map, $\psi : O^{\mathrm{nr}} \to B$ an $\mathcal{O}$-algebra map, $E$ a fake elliptic curve over $B$, $E'$ one over $B'$, and $g : E'.A \to E.A$ a morphism of schemes satisfying `FakeEllipticCurve.IsPullbackVia` for the underlying ring map of $\varphi$: the square formed by $g$, the structure morphisms and $\mathrm{Spec}(\varphi)$ is cartesian, $g$ carries the relative group law of $E'$ to that of $E$ after base change, $g$ intertwines the $\Lambda$-actions, and every point of $E'$ factoring through the level morphism of $E'$ has its image under $g$ factoring through that of $E$. Given a rigidification $\rho$ of $E$ relative to $\psi$ — a fake elliptic curve $\rho.Eb$ over $B/(\pi)$ realised as a pullback of $E$ along reduction with comparison map $\rho.gb$, a fake elliptic curve $\rho.Ab$ over $B/(\pi)$ realised as a pullback of $A_0$ along the map $O^{\mathrm{nr}}/(\pi) \to B/(\pi)$ induced by $\psi$ with comparison $\rho.gA$, an exponent $\rho.d$, and mutually inverse-up-to-$r^{\rho.d}$ isogenies $\rho.\varphi, \rho.\varphi'$ between $\rho.Eb$ and $\rho.Ab$ over $B/(\pi)$ preserving the level structure — the assertion is that there exists a rigidification $\rho'$ of $E'$ relative to $\varphi \circ \psi$ which is a pullback of $\rho$ in the sense of `Rigidification.IsPullbackVia`: there are morphisms $u_b : \rho'.Eb.A \to \rho.Eb.A$ and $u_A : \rho'.Ab.A \to \rho.Ab.A$ exhibiting $\rho'.Eb$ and $\rho'.Ab$ as pullbacks of $\rho.Eb$ and $\rho.Ab$ along the map $B/(\pi) \to B'/(\pi)$ induced by $\varphi$, with $u_b$ followed by $\rho.gb$ equal to $\rho'.gb$ followed by $g$, $u_A$ followed by $\rho.gA$ equal to $\rho'.gA$, $\rho'.d = \rho.d$, and $u_b$ followed by $\rho.\varphi$ equal to $\rho'.\varphi$ followed by $u_A$.
--
--   This is the functoriality of rigidification data in the coefficient algebra: the $\pi$-adic rigidifications used in the Čerednik–Drinfel'd description of fake elliptic curves form a functor on $\mathcal{O}$-algebras, compatible with pullback of the curves themselves. It is the base-change step used throughout the subsequent analysis of full level structures and norm level transport on rigidified families.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia
    {r N : ℕ}
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (B B' : Type) [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
    (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B) (E' : FakeEllipticCurve Λ N B') (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E E' g)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) :
    ∃ ρ' : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) E',
      FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ρ ρ' := by sorry
