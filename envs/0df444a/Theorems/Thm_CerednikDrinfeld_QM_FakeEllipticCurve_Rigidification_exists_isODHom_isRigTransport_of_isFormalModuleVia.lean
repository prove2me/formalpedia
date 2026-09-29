-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isODHom_isRigTransport_of_isFormalModuleVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isODHom_isRigTransport_of_isFormalModuleVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/2c8e04a4-18d7-5c73-ad9b-44be19929705
-- title:
--   Transport datum from the quasi-inverse leg of a rigidification
-- statement:
--   Fix a prime $r$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, and a map $\mathrm{coord}\colon\Lambda\to \mathrm{Zp2}\,r\times \mathrm{Zp2}\,r$ (values in Witt vectors of $\mathbb F_{r^2}$) whose image is $r$-adically dense, in the sense that for all $k$ and all $\alpha,\beta$ there is $m\in\Lambda$ with both components of $\mathrm{coord}\,m$ congruent to $\alpha,\beta$ modulo $r^k$. Let $\mathcal O$ be a commutative ring and $\pi\in\mathcal O$ with $(\pi)=(r)$, let $O^{nr}$ be an $\mathcal O$-algebra, let $A_0$ be a `FakeEllipticCurve` for $\Lambda,N$ over $O^{nr}/(\pi)$, let $X_0$ be a `FormalODModule` for $r$ over $O^{nr}/(\pi)$ and $\theta_0$ a system of formal coordinates in $2$ variables for $A_0.f$ with $A_0.\mathrm{IsFormalModuleVia}\ \mathrm{coord}\ X_0\ \theta_0$, i.e. $\theta_0$ are formal coordinates for the relative group law of $A_0$ with formal group $X_0.F$, and for $m\in\Lambda$ the action of $m$ on points is computed on coordinates by $\mathrm{addVia}\ X_0.F\ (X_0.\mathrm{act}(\mathrm{coord}\,m)_1)\ ((X_0.\mathrm{act}(\mathrm{coord}\,m)_2)\circ X_0.\varpi)$. Let $\kappa\colon O^{nr}/(\pi)\to O^{nr}/(r)$ be a ring map compatible with the two projections from $O^{nr}$. Let $B$ be an $\mathcal O$-algebra, $\psi\colon O^{nr}\to B$ an $\mathcal O$-algebra map, $E$ a fake elliptic curve over $B$, $\rho$ a rigidification of $E$ relative to $A_0$ and $\psi$ (reductions $\rho.E_b$ of $E$ and $\rho.A_b$ of $A_0$ over $\bar B=B/(\pi)$ with comparison maps $\rho.g_b$, $\rho.g_A$ realising pull-back squares, together with a level-preserving $\Lambda$-equivariant isogeny pair $\rho.\varphi,\rho.\varphi'$ of degree $r^{\rho.d}$), and let $X,\theta$ exhibit $X$ as the formal module of $E$ via $\mathrm{coord}$. Then there exist a ring map $\kappa_B\colon \bar B\to B/(r)$ and a pair $\sigma$ of power series in two variables over $\bar B$ such that: $\kappa_B$ is compatible with the two projections from $B$; $\kappa_B$ composed with the map $\bar\psi\colon O^{nr}/(\pi)\to\bar B$ induced by $\psi$ equals $\kappa$ followed by the map $O^{nr}/(r)\to B/(r)$ induced by $\psi$; $\sigma$ is a homomorphism of formal $\mathcal O_D$-modules from $X_0$ base changed along $\bar\psi$ to $X$ base changed along $B\to\bar B$ (a homomorphism of the formal group laws commuting with the $\mathrm{Zp2}\,r$-actions and with $\varpi$); for every commutative ring $B''$ that is an algebra over $\bar B$, over $B$ and over $O^{nr}/(\pi)$ with the structure maps from $B$ and from $O^{nr}/(\pi)$ factoring through $\bar B$ as stated, every ideal $J\subseteq B''$ with $J^{m+1}=0$, every $s\colon \mathrm{Fin}\,2\to J$ and every $B''$-point $P_A$ of $\rho.A_b$ over the structure map with $P_A$ followed by $\rho.g_A$ equal to $\theta_0(B'',s)$, the composite of $P_A$ with $\rho.\varphi'$ and $\rho.g_b$ equals $\theta(B'',\ \cdot\ )$ evaluated at the truncations $\mathrm{nilEval}\ m\ (\sigma_i)\ s$; and finally, for every formal $\mathcal O_D$-module $\Phi$ over $O^{nr}/(r)$, every pair of series $\beta_0$ over $O^{nr}/(r)$ and all $j,n$, the rigidified datum with underlying module $X$, integer $n$ and series $(\mathrm{Series.map}\ \kappa_B\ \sigma)\circ\big((\mathrm{Series.map}\ \bar\psi_r\ \beta_0)\circ (X_i^{r^j})\big)$ satisfies $\mathrm{IsRigTransport}\ \theta_0\ \kappa\ \beta_0\ \rho\ \theta\ j$.
--
--   This is the functoriality of the formal $\mathcal O_D$-module of a fake elliptic curve — formal completion along the unit sections — applied to the quasi-inverse leg $\varphi'$ of a rigidification, after reducing $\theta_0$ and $\theta$ to $B/(\pi)$ along the two pull-back squares. It supplies the transport datum used to pass from rigidified fake elliptic curves to Drinfeld's moduli of rigidified special formal $\mathcal O_D$-modules in the Čerednik–Drinfeld uniformisation, and is cited by the admissibility and Frobenius-twist steps of that comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isODHom_isRigTransport_of_isFormalModuleVia.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isODHom_isRigTransport_of_isFormalModuleVia
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

    (coord : ↥Λ → Zp2 r × Zp2 r)
    (hdense : ∀ (k : ℕ) (α β : Zp2 r), ∃ m : ↥Λ,
      (coord m).1 - α ∈ Ideal.span {((r : Zp2 r)) ^ k} ∧ (coord m).2 - β ∈ Ideal.span {((r : Zp2 r)) ^ k})

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]

    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))

    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hE : E.IsFormalModuleVia coord X θ) :
    ∃ (κB : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B ⧸ pIdeal r B))
      (σ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})),

      κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) = Ideal.Quotient.mk (pIdeal r B) ∧
      κB.comp (Rigidification.residueLeg π ψ) = (residueMap (ψ : Onr →+* B)).comp κ ∧

      FormalODModule.IsODHom (X₀.map (Rigidification.residueLeg π ψ))
        (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) σ ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
          [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
          algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
          algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
            (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Rigidification.residueLeg π ψ) →
          ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
              PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
              PA ≫ ρ.gA = (θ₀ B'' s).1 →
                PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1) ∧

      ∀ (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr)) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (j n : ℕ),
        Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j
          ({ X := X, n := n,
             ρ := (Series.map κB σ).comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
               (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j))) } :
            Rigidified r Φ B) := by sorry
