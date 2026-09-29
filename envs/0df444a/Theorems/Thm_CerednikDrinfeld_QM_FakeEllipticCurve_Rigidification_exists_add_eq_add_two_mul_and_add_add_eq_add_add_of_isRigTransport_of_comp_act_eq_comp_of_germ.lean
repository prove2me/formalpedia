-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_of_comp_act_eq_comp_of_germ
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_of_comp_act_eq_comp_of_germ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/976dd711-4db4-5bfb-94d9-69996da80c32
-- title:
--   Exponent bookkeeping for two transports of a rigidification
-- statement:
--   Fix a prime $r$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $\mathcal O^{\mathrm{nr}}$ with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ containing every rational integer, a level $N$, and a map $\mathrm{coord}:\Lambda\to W(\mathbb F_{r^2})\times W(\mathbb F_{r^2})$ satisfying `IsOrderCoord` (additive, injective, dense image, $1\mapsto(1,0)$, Frobenius-twisted multiplicativity, and the trace condition). Over $\mathcal O^{\mathrm{nr}}/(\pi)$ take a fake elliptic curve $A_0$ for $(\Lambda,N)$, a formal $\mathcal O_D$-module $X_0$ of dimension $2$ and formal coordinates $\theta_0$ for $A_0$ with $A_0$ a formal module via $(\mathrm{coord},X_0,\theta_0)$; a ring map $\iota:W(\mathbb F_{r^2})\to\mathcal O^{\mathrm{nr}}$, a formal $\mathcal O_D$-module $\Phi$ over $\mathcal O^{\mathrm{nr}}/(r)$, a ring map $\kappa:\mathcal O^{\mathrm{nr}}/(\pi)\to\mathcal O^{\mathrm{nr}}/(r)$, and $\mathcal O_D$-homomorphisms $\beta_0:\Phi\to X_0\otimes_\kappa$, $\beta_0':X_0\otimes_\kappa\to\Phi$ with $\beta_0\circ\beta_0'$ the action of $r^{N_0}$. Over a nontrivial Noetherian $\mathcal O$-algebra $B$ with $\psi:\mathcal O^{\mathrm{nr}}\to B$, $(\pi)=(r)$ in $B$ and $\pi$ nilpotent in $B$, take a fake elliptic curve $E$, a formal $\mathcal O_D$-module $X$ and coordinates $\theta$ with $E$ a formal module via $(\mathrm{coord},X,\theta)$, and two rigidifications $\rho,\rho'$ of $E$ along $A_0$ and $\psi$. Assume given $j,j'\le1$ and rigidified objects $t=(X,n_t,\rho_t)$, $t'=(X,n_{t'},\rho_{t'})$ over $B$ with $t.X=t'.X=X$, which are `IsRigTransport` of $\rho$ resp. $\rho'$ with respect to $\theta_0,\kappa,\beta_0,\theta$ at parameters $j$ resp. $j'$, and which are admissible for $\iota$ and the twisted legs $\psi\circ\mathrm{Fr}^{-j}$, $\psi\circ\mathrm{Fr}^{-j'}$ (special, of height $4$, with $\rho_t$ an isogeny of height $4n_t$, similarly for $t'$). Assume a comparison pair $(u,u_A)$ between $\rho'$ and $\rho$ (identity-base pullbacks compatible with $g_b$ and $g_A$), an endomorphism $f'$ of $A_0$ over its base, a lift $f'_b$ of $f'$ on $\rho.A_b$ over its base, and natural numbers $e_a,e_c$ with $\rho'.\varphi'$ followed by $u$ followed by the $\Lambda$-action of $r^{e_a}$ on $\rho.E_b$ equal to $u_A$ followed by $f'_b$, $\rho.\varphi'$ and the action of $r^{e_c}$. Finally let $\varepsilon'$ be an endomorphism of the formal group law of $X_0$ which is the germ of $f'$ in the coordinates $\theta_0$ (for all nilpotent-ideal data, $\theta_0$ of the truncated evaluation of $\varepsilon'$ at $s$ equals $f'$ applied to $\theta_0(s)$), set $e'=\beta_0'\circ(\kappa_*\varepsilon')\circ\beta_0$, and suppose the image of $e'$ under the residue map of $\psi$ has kernel of degree $r^{2m'}$ (finite projective kernel algebra of that rank over every field). Then there exists $k\in\mathbb N$ with $j'+m'=j+2k$ and $n_t+k+e_c=n_{t'}+N_0+e_a$.
--
--   This is the numerical part of the dictionary between curve-level identities and formal-module identities in the Čerednik–Drinfeld uniformisation: a single curve-level relation between two rigidifications, twisted by an endomorphism of the base fake elliptic curve and by powers of $r$, is converted into two equations among the parity $j$, the transport levels $n_t$, the isogeny degrees $N_0$, $m'$ and the exponents $e_a$, $e_c$. It is used in the construction of the action on the rigidified moduli functor, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_isActBy_rigidifiedToG_star_of_isTranslateBy_of_isLevelIsogeny_of_isAtkinLehnerQuotient_of_endIsoFull`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_isActBy_rigidifiedToG_star_of_isTranslateBy_of_isLevelIsogeny_of_isAtkinLehnerQuotient_of_endIsoFull).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_of_comp_act_eq_comp_of_germ.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_of_comp_act_eq_comp_of_germ
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪)
    {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (ι : Zp2 r →+* Onr) (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ β₀' : Series (Onr ⧸ pIdeal r Onr)) (N₀ : ℕ)
    (hβ₀ : FormalODModule.IsODHom Φ (X₀.map κ) β₀) (hβ₀' : FormalODModule.IsODHom (X₀.map κ) Φ β₀')
    (h₂ : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N₀))

    {B : Type} [CommRing B] [IsNoetherianRing B] [Nontrivial B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (hπB : Ideal.span {algebraMap 𝒪 B π} = pIdeal r B) (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hE : E.IsFormalModuleVia coord X θ)
    (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E)

    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j t)
    (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    (j' : ℕ) (t' : Rigidified r Φ B) (hj' : j' ≤ 1) (ht'X : t'.X = X)
    (htr' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ' θ j' t')
    (hadm' : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j' : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))

    (u : ρ'.Eb.A ⟶ ρ.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (hcmp : FakeEllipticCurve.Rigidification.IsComparison ρ ρ' u uA)
    (f' : A₀.A ⟶ A₀.A) (hf' : f' ≫ A₀.f = A₀.f)
    (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (hf'b : f'b ≫ ρ.gA = ρ.gA ≫ f') (hf'bf : f'b ≫ ρ.Ab.f = ρ.Ab.f)
    (ea ec : ℕ)
    (hcurve : ρ'.φ' ≫ u ≫ ρ.Eb.act ⟨(((r ^ ea : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      uA ≫ f'b ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ ec : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (ε' : MvFormalGroup.End X₀.F)
    (hε' : ∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
      J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s) = mapPt f' hf' (θ₀ B' s))
    (e' : Series (Onr ⧸ pIdeal r Onr)) (he' : e' = β₀'.comp ((Series.map κ ε'.toPowerSeries).comp β₀))
    (m' : ℕ) (hker : FormalODModule.HasKernelOfDegree (Series.map (residueMap (ψ : Onr →+* B)) e') (r ^ (2 * m'))) :
    ∃ k : ℕ, j' + m' = j + 2 * k ∧ t.n + k + ec = t'.n + N₀ + ea := by sorry
