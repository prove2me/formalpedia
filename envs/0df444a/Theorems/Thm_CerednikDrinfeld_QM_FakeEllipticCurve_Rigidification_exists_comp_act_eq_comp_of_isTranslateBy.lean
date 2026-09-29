-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_of_isTranslateBy
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_comp_act_eq_comp_of_isTranslateBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/25be36d5-657b-5eb1-ac0f-253ce585858a
-- title:
--   Translating a rigidification, read on the dual isogenies
-- statement:
--   Fix a natural number $r$, a commutative ring $\mathcal O$ with an element $\pi$, a commutative $\mathcal O$-algebra $Onr$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ and a level $N$, and assume ($hΛℤ$) that every rational integer lies in $\Lambda$. Let $A_0$ be a fake elliptic curve with $\Lambda$-action and level data over $Onr/(\pi)$, let $B$ be a commutative $\mathcal O$-algebra with an $\mathcal O$-algebra map $\psi : Onr \to B$, and let $E$ be a fake elliptic curve over $B$. Let $\rho,\rho'$ be rigidifications of $E$ relative to $A_0$ and $\psi$: each consists of a curve $E_b$ over $B/(\pi)$ pulling back $E$ along $B \to B/(\pi)$ via $g_b$, a curve $A_b$ over $B/(\pi)$ pulling back $A_0$ along the map induced by $\psi$ via $g_A$, an exponent $d$, and morphisms $\varphi : E_b \to A_b$ (over the structure morphisms, preserving level points) and $\varphi' : A_b \to E_b$ forming an isogeny pair of degree $r^{d}$, that is, additive on $T$-points, $\Lambda$-equivariant, with both composites equal to the action of $r^{d} \in \Lambda$. Let $f,f' : A_0.A \to A_0.A$ be an isogeny pair of degree $r^{d_\gamma}$ on $A_0$ in the same sense, and assume $\rho'$ is the translate of $\rho$ by $f$: there are $u : \rho'.E_b \to \rho.E_b$ and $u_A : \rho'.A_b \to \rho.A_b$ which are a comparison of $\rho$ with $\rho'$ (each exhibits the source as a pullback along the identity of $B/(\pi)$, compatibly with group law, $\Lambda$-action and level points, and $u \circ$-composed with $\rho.g_b$, resp. $u_A$ with $\rho.g_A$, gives $\rho'.g_b$, resp. $\rho'.g_A$), together with $e_{\gamma b} : \rho.A_b \to \rho.A_b$ lying over the structure morphism and satisfying $e_{\gamma b}$ followed by $\rho.g_A$ equals $\rho.g_A$ followed by $f$, and exponents making $u$, $\rho.\varphi$, $e_{\gamma b}$ agree with $\rho'.\varphi$, $u_A$ up to powers of $r$ acting through $\Lambda$. The conclusion asserts the existence of a comparison pair $(u,u_A)$ of $\rho$ and $\rho'$, a morphism $f'_b : \rho.A_b \to \rho.A_b$ with $f'_b$ followed by $\rho.g_A$ equal to $\rho.g_A$ followed by $f'$ and $f'_b$ lying over the structure morphism of $\rho.A_b$, and natural numbers $i,j$ such that $\rho'.\varphi'$ followed by $u$ followed by the action of $r^{i}$ on $\rho.E_b$ equals $u_A$ followed by $f'_b$, then $\rho.\varphi'$, then the action of $r^{j}$ on $\rho.E_b$.
--
--   This is the dual counterpart of the statement that $\rho'$ is a translate of $\rho$ by a self-isogeny $f$ of the base fake elliptic curve $A_0$: the same comparison data relate the dual isogenies $\varphi'$ through the base change $f'_b$ of the dual isogeny $f'$, again only up to powers of $r$ acting through $\Lambda$. It feeds the construction of the action on rigidified objects used in the Čerednik–Drinfeld uniformisation package, being cited in the analysis of Atkin–Lehner quotients and level isogenies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_of_isTranslateBy.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_comp_act_eq_comp_of_isTranslateBy
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ρ ρ' : Rigidification r π A₀ ψ E) (f f' : A₀.A ⟶ A₀.A) (dγ : ℕ)
    (hff' : FakeEllipticCurve.IsIsogenyPair (r ^ dγ) A₀ A₀ f f') (htr : Rigidification.IsTranslateBy hΛℤ f ρ ρ') :
    ∃ (u : ρ'.Eb.A ⟶ ρ.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : Rigidification.IsComparison ρ ρ' u uA)
      (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (_ : f'b ≫ ρ.gA = ρ.gA ≫ f') (_ : f'b ≫ ρ.Ab.f = ρ.Ab.f) (i j : ℕ),
      ρ'.φ' ≫ u ≫ ρ.Eb.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        uA ≫ f'b ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
