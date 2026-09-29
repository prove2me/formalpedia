-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isRigTransport_comp_nilEval_of_isRigTransport_of_isODHom_of_constantCoeff_eq_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isRigTransport_comp_nilEval_of_isRigTransport_of_isODHom_of_constantCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/66e0f7c5-1f6f-580c-8759-66efaae15aa7
-- title:
--   Transport of rigidifications along an isomorphism of formal 𝒪_D-modules
-- statement:
--   Let $r$ be a prime, $a,b\in\mathbb{Q}$, $\Lambda$ a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ and $N\in\mathbb{N}$. Let $\mathcal{O}$ be a commutative ring, $\pi\in\mathcal{O}$, $O^{\mathrm{nr}}$ an $\mathcal{O}$-algebra, $A_0$ a fake elliptic curve of level $N$ with $\Lambda$-action over $O^{\mathrm{nr}}/(\pi)$ carrying formal coordinates $\theta_0$ in two variables (a rule assigning to each algebra $B'$ and each pair $s\in (B')^2$ a $B'$-point of $A_0$ over $B'$), $\kappa:O^{\mathrm{nr}}/(\pi)\to O^{\mathrm{nr}}/(r)$ a ring homomorphism and $\beta_0$ a pair of power series in two variables over $O^{\mathrm{nr}}/(r)$. Let $B$ be an $\mathcal{O}$-algebra, $\psi:O^{\mathrm{nr}}\to B$ an $\mathcal{O}$-algebra map, $E$ a fake elliptic curve over $B$, $\rho$ a rigidification of $E$ relative to $A_0$ and $\psi$ (a reduction $E_b$ of $E$ modulo $\pi$, a pullback $A_b$ of $A_0$ along the induced map of residue rings, and an $r^d$-isogeny pair $\varphi,\varphi'$ between $E_b$ and $A_b$ preserving the level structure), $\theta$ formal coordinates for $E$ in two variables, $j\in\mathbb{N}$, $\Phi$ a formal $\mathcal{O}_D$-module over $O^{\mathrm{nr}}/(r)$, and $t=(X,\,t.n,\,\rho_t)$ a rigidified datum over $B$ for $\Phi$, consisting of a formal $\mathcal{O}_D$-module $X$ over $B$, a natural number, and a pair of power series $\rho_t$ over $B/(r)$. Assume `IsRigTransport θ₀ κ β₀ ρ θ j t`, i.e. there are a ring homomorphism $\kappa_B:B/(\pi)\to B/(r)$ and a pair of series $\sigma$ over $B/(\pi)$ such that $\kappa_B$ is compatible with the reduction maps out of $B$ and intertwines $\kappa$ with the map $B/(\pi)\to B/(r)$ induced by $\psi$; such that on nilpotent points $s$ of any suitably compatible $B''$ (with $J^{m+1}=0$, $s\in J^2$) every point $P_A$ of $A_b$ lying over $\theta_0(s)$ via $\rho.gA$ satisfies $P_A$ followed by $\varphi'$ and then by $\rho.gb$ equals $\theta$ evaluated at the truncated values $\mathrm{nilEval}_m(\sigma)(s)$; and such that $\rho_t$ is the substitution of the reduction of $\beta_0$ composed with $X_i\mapsto X_i^{r^j}$ into $\kappa_B\sigma$. Assume further that $(r)=(\pi)$ in $\mathcal{O}$ and that all components of $\beta_0$ and of $\rho_t$ have vanishing constant coefficient. Let $Y$ be a formal $\mathcal{O}_D$-module over $B$ and $u,v$ pairs of power series over $B$ which are homomorphisms $X\to Y$ and $Y\to X$ of formal $\mathcal{O}_D$-modules (homomorphisms of the underlying two-variable formal group laws commuting with the action of `Zp2 r` and with the series $\varpi$) and are mutually inverse, $v\circ u=u\circ v=\mathrm{id}$. Finally let $\theta'$ be formal coordinates for $E$ in two variables such that for every $B$-algebra $B''$, every ideal $J$ with $J^{n+1}=0$ for some $n$, and every $s\in J^2$, one has $\theta'(s)=\theta\bigl(\mathrm{nilEval}_n(v)(s)\bigr)$. Then `IsRigTransport θ₀ κ β₀ ρ θ' j` holds for the rigidified datum with module $Y$, the same natural number $t.n$, and series obtained by substituting $\rho_t$ into the reduction of $u$ modulo $(r)$.
--
--   This is the functoriality of Drinfeld transport of a rigidification under an isomorphism of the associated formal $\mathcal{O}_D$-module, matched by the corresponding change of formal coordinates on the fake elliptic curve. It is used in the comparison of rigidified fake elliptic curves with rigidified formal $\mathcal{O}_D$-modules, feeding into [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.parity_eq_and_isIsomorphic_of_isRigTransport_of_isPullbackVia_corr_of_rigidified`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.parity_eq_and_isIsomorphic_of_isRigTransport_of_isPullbackVia_corr_of_rigidified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isRigTransport_comp_nilEval_of_isRigTransport_of_isODHom_of_constantCoeff_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isRigTransport_comp_nilEval_of_isRigTransport_of_isODHom_of_constantCoeff_eq_zero
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ : Series (Onr ⧸ pIdeal r Onr))

    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (j : ℕ)
    {Φ : FormalODModule r (Onr ⧸ pIdeal r Onr)} (t : Rigidified r Φ B)
    (ht : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j t)

    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hβ₀c : ∀ i, MvPowerSeries.constantCoeff (β₀ i) = 0)
    (hρc : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0)

    (Y : FormalODModule r B) (u v : Series B)
    (hu : FormalODModule.IsODHom t.X Y u) (hv : FormalODModule.IsODHom Y t.X v)
    (hvu : v.comp u = Series.id B) (huv : u.comp v = Series.id B)
    (θ' : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hθ' : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        θ' B'' s = θ B'' (fun i => MvFormalGroup.nilEval n (v i) s)) :
    FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ' j
      ({ X := Y, n := t.n, ρ := (u.map (Ideal.Quotient.mk (pIdeal r B))).comp t.ρ } : Rigidified r Φ B) := by sorry
