-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslateBy_of_isPullbackVia_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslateBy_of_isPullbackVia_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/f14fe3fc-9933-5847-b84d-f4254a302349
-- title:
--   Translation of rigidifications is stable under base change
-- statement:
--   Fix a natural number $r$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $O^{nr}$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ and a natural number $N$; assume every rational integer lies in $\Lambda$ (hypothesis `hΛℤ`) and that $N$ is a unit in $\mathcal O$. Let $A_0$ be a fake elliptic curve with $\Lambda$-action and level-$N$ data over $O^{nr}/(\pi)$ in the sense of `FakeEllipticCurve`, let $B$ be an $\mathcal O$-algebra with an $\mathcal O$-algebra map $\psi : O^{nr} \to B$, let $E$ be a fake elliptic curve over $B$, and let $f$ be an endomorphism of the scheme $A_0.A$ (no compatibility with the structure of $A_0$ being required). Let $\rho,\rho'$ be rigidifications of $E$ relative to $A_0$, $\psi$, $r$ and $\pi$, i.e. data consisting of fake elliptic curves $E_b, A_b$ over $B/(\pi)$ presented as pullbacks of $E$ and of $A_0$ along the reduction map and along the map induced by $\psi$, together with an exponent $d$ and an isogeny pair $\varphi,\varphi'$ of degree $r^d$ between $E_b$ and $A_b$ respecting the level structure. Assume $\rho'$ is the translate of $\rho$ by $f$: there are morphisms $u : \rho'.E_b.A \to \rho.E_b.A$ and $u_A : \rho'.A_b.A \to \rho.A_b.A$ forming a comparison pair in the sense of the predicate `IsComparison`, together with an endomorphism $e_{\gamma b}$ of $\rho.A_b.A$ satisfying $e_{\gamma b}$ followed by $\rho.gA$ equal to $\rho.gA$ followed by $f$ and lying over the base, and natural numbers $i,j$ with $u$ followed by $\rho.\varphi$, $e_{\gamma b}$ and the action of $r^i$ equal to $\rho'.\varphi$ followed by $u_A$ and the action of $r^j$. Let further $L$ be an $\mathcal O$-algebra, $\varphi : B \to L$ an $\mathcal O$-algebra map, $E_L$ a fake elliptic curve over $L$ and $g : E_L.A \to E.A$ exhibiting $E_L$ as a pullback of $E$ along $\varphi$ in the sense of `FakeEllipticCurve.IsPullbackVia` (cartesian square over $\operatorname{Spec}$ of $\varphi$, compatibility of $g$ with the relative group laws and with the $\Lambda$-actions, and descent of level points). Finally let $\rho_L,\rho_L'$ be rigidifications of $E_L$ relative to $\varphi\circ\psi$ which are pullbacks of $\rho$ and of $\rho'$ along $\varphi$ via $g$ in the sense of `Rigidification.IsPullbackVia` (comparison maps of the $E_b$- and $A_b$-legs which are pullbacks along the induced map of $\pi$-reductions, compatible with $gb$, $g$ and $gA$, equality of the exponents $d$, and compatibility with the isogenies $\varphi$). The conclusion is that $\rho_L'$ is again the translate of $\rho_L$ by $f$, in the same sense.
--
--   This is the functoriality, under base change of the coefficient ring, of the relation 'one rigidification is the $f$-translate of another' for fake elliptic curves, a bookkeeping step in the Čerednik–Drinfeld $p$-adic uniformisation of Shimura curves. It is used in the construction of the induced action on rigidified isogeny classes at Atkin–Lehner quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslateBy_of_isPullbackVia_of_isPullbackVia.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslateBy_of_isPullbackVia_of_isPullbackVia
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hN : IsUnit ((N : ℕ) : 𝒪))
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (f : A₀.A ⟶ A₀.A) (ρ ρ' : Rigidification r π A₀ ψ E)
    (htr : Rigidification.IsTranslateBy hΛℤ f ρ ρ')
    {L : Type} [CommRing L] [Algebra 𝒪 L] (φ : B →ₐ[𝒪] L)
    {EL : FakeEllipticCurve Λ N L} (g : EL.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* L) E EL g)
    (ρL ρL' : Rigidification r π A₀ (φ.comp ψ) EL)
    (hρL : Rigidification.IsPullbackVia φ g hg ρ ρL) (hρL' : Rigidification.IsPullbackVia φ g hg ρ' ρL') :
    Rigidification.IsTranslateBy hΛℤ f ρL ρL' := by sorry
