-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isPullbackVia_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_corr_of_isPullbackVia_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/b2dc0820-beab-5f41-ba77-a308e1ec1211
-- title:
--   Correspondence packages between rigidifications pull back along base change
-- statement:
--   Fix $r\in\mathbb N$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $O^{nr}$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ and $N\in\mathbb N$; assume every rational integer lies in $\Lambda$ and that $N$ is a unit in $\mathcal O$. Let $A_0$ be a fake elliptic curve for $(\Lambda,N)$ over $O^{nr}/(\pi)$, let $B$ be an $\mathcal O$-algebra with an $\mathcal O$-algebra map $\psi:O^{nr}\to B$, let $E,E_f$ be fake elliptic curves over $B$, let $q:E.A\to E_f.A$ be a scheme morphism and $f_0:A_0.A\to A_0.A$ an endomorphism. Let $\rho,\rho_f$ be rigidifications of $E,E_f$ relative to $(r,\pi,A_0,\psi)$: each consists of a fake elliptic curve $E_b$ over $B/(\pi)$ together with $g_b$ exhibiting it as the base change of $E$ along $B\to B/(\pi)$ (cartesian square, compatible relative group law, $\Lambda$-action and level structure), a fake elliptic curve $A_b$ over $B/(\pi)$ with $g_A$ exhibiting it as the base change of $A_0$ along the map $O^{nr}/(\pi)\to B/(\pi)$ induced by $\psi$, an exponent $d$, and a level-preserving pair $\varphi,\varphi'$ between $E_b$ and $A_b$ forming an $r^d$-isogeny pair. Assume the correspondence package over $B$: there are $q_b:\rho.E_b.A\to\rho_f.E_b.A$ with $q_b\circ$ (i.e. followed by) $\rho_f.g_b$ equal to $\rho.g_b$ followed by $q$ and $q_b$ over $B/(\pi)$; a morphism $u_A:\rho_f.A_b.A\to\rho.A_b.A$ which is an identity-base-change pullback comparison of $\rho.A_b$ and $\rho_f.A_b$ with $u_A$ followed by $\rho.g_A$ equal to $\rho_f.g_A$; a morphism $e_b$ of $\rho.A_b.A$ over $B/(\pi)$ lifting $f_0$ along $\rho.g_A$; and natural numbers $i,j$ with $q_b\,\rho_f.\varphi\,u_A\,[r^i]=\rho.\varphi\,e_b\,[r^j]$, where $[r^k]$ denotes the action of the integer $r^k\in\Lambda$ on $\rho.A_b$. Further let $\phi:B\to L$ be an $\mathcal O$-algebra map, let $E_L,E_{f,L}$ be fake elliptic curves over $L$ with $g,g_f$ exhibiting them as base changes of $E,E_f$ along $\phi$, let $\rho_L,\rho_{f,L}$ be rigidifications over $(\phi\circ\psi)$ which are pullbacks of $\rho,\rho_f$ in the sense of `Rigidification.IsPullbackVia` (comparison maps on the $E_b$- and $A_b$-legs compatible with $g$, $g_f$, $g_b$, $g_A$ and $\varphi$, equal exponents $d$), and let $q_L:E_L.A\to E_{f,L}.A$ satisfy $q_L$ followed by $g_f$ equals $g$ followed by $q$, and $q_L$ be a morphism over $L$. Then the correspondence package holds over $L$: such $q_b$, $u_A$, $e_b$ and exponents exist for $\rho_L,\rho_{f,L},q_L,f_0$, with the same $i$ and $j$.
--
--   This is the base-change (descent along a ring map $B\to L$) statement for the correspondence data that couple two rigidifications of fake elliptic curves near a supersingular point in the Čerednik–Drinfeld setting. It is used to read the equivariance clauses of the supersingular dictionary on a base change of the curves, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_isActBy_rigidifiedToG_star_of_isTranslateBy_of_isLevelIsogeny_of_isAtkinLehnerQuotient_of_endIsoFull`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_isActBy_rigidifiedToG_star_of_isTranslateBy_of_isLevelIsogeny_of_isAtkinLehnerQuotient_of_endIsoFull).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isPullbackVia_of_isPullbackVia.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_corr_of_isPullbackVia_of_isPullbackVia
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hN : IsUnit ((N : ℕ) : 𝒪))
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E Ef : FakeEllipticCurve Λ N B}
    (q : E.A ⟶ Ef.A) (f₀ : A₀.A ⟶ A₀.A)
    (ρ : Rigidification r π A₀ ψ E) (ρf : Rigidification r π A₀ ψ Ef)
    (hcorr : ∃ (qb : ρ.Eb.A ⟶ ρf.Eb.A) (_ : qb ≫ ρf.gb = ρ.gb ≫ q) (_ : qb ≫ ρf.Eb.f = ρ.Eb.f)
      (uA : ρf.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (_ : uA ≫ ρ.gA = ρf.gA)
      (eb : ρ.Ab.A ⟶ ρ.Ab.A) (_ : eb ≫ ρ.gA = ρ.gA ≫ f₀) (_ : eb ≫ ρ.Ab.f = ρ.Ab.f)
      (i j : ℕ),
      qb ≫ ρf.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ eb ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    {L : Type} [CommRing L] [Algebra 𝒪 L] (φ : B →ₐ[𝒪] L)
    {EL EfL : FakeEllipticCurve Λ N L}
    (g : EL.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* L) E EL g)
    (gf : EfL.A ⟶ Ef.A) (hgf : FakeEllipticCurve.IsPullbackVia (φ : B →+* L) Ef EfL gf)
    (ρL : Rigidification r π A₀ (φ.comp ψ) EL) (ρfL : Rigidification r π A₀ (φ.comp ψ) EfL)
    (hρL : Rigidification.IsPullbackVia φ g hg ρ ρL) (hρfL : Rigidification.IsPullbackVia φ gf hgf ρf ρfL)
    (qL : EL.A ⟶ EfL.A) (hqL : qL ≫ gf = g ≫ q) (hqLf : qL ≫ EfL.f = EL.f) :
    ∃ (qb : ρL.Eb.A ⟶ ρfL.Eb.A) (_ : qb ≫ ρfL.gb = ρL.gb ≫ qL) (_ : qb ≫ ρfL.Eb.f = ρL.Eb.f)
      (uA : ρfL.Ab.A ⟶ ρL.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρL.Ab ρfL.Ab uA) (_ : uA ≫ ρL.gA = ρfL.gA)
      (eb : ρL.Ab.A ⟶ ρL.Ab.A) (_ : eb ≫ ρL.gA = ρL.gA ≫ f₀) (_ : eb ≫ ρL.Ab.f = ρL.Ab.f)
      (i j : ℕ),
      qb ≫ ρfL.φ ≫ uA ≫ ρL.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρL.φ ≫ eb ≫ ρL.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
