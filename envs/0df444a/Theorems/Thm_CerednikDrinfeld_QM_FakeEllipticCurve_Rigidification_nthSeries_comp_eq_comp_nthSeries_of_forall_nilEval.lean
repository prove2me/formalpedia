-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/fc1961e9-f446-5dfd-b80f-9ce8f2660be4
-- title:
--   Integer multiplication commutes with the series representing φ'
-- statement:
--   Fix a prime $r$, a commutative ring $\mathcal O$ with an element $\pi$, and an $\mathcal O$-algebra $O^{nr}$; write $k_0 = O^{nr}/(\pi)$. Let $a,b \in \mathbb Q$, let $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule containing the image of every integer, let $N \in \mathbb N$, and let $\mathrm{coord} : \Lambda \to \mathbb{Z}_{p^2}\text{-pairs} = W(\mathbb F_{r^2})\times W(\mathbb F_{r^2})$ satisfy `IsOrderCoord`: additive, sending $1$ to $(1,0)$, multiplicative for the Frobenius-twisted product rule, injective, with dense image modulo all powers of $r$, and compatible with reduced traces. Let $A_0$ be a fake elliptic curve over $k_0$ for $(\Lambda,N)$, $X_0$ a formal $\mathcal O_D$-module of height data `FormalODModule r` over $k_0$, and $\theta_0$ a system of two-dimensional formal coordinates for $A_0.f$ exhibiting $X_0$ via $\mathrm{coord}$, i.e. $\theta_0$ are formal coordinates for $A_0.L$ with formal group $X_0.F$ and each $m \in \Lambda$ acts on coordinates by $\mathrm{addVia}\,X_0.F\,(X_0.\mathrm{act}\,(\mathrm{coord}\,m)_1)\,((X_0.\mathrm{act}\,(\mathrm{coord}\,m)_2)\circ X_0.\varpi)$. Let $B$ be an $\mathcal O$-algebra, $\psi : O^{nr} \to B$ an $\mathcal O$-algebra map, and let $E$, $X$, $\theta$ be the corresponding data over $B$ with $E$ a formal module via $\mathrm{coord}$. Let $\rho$ be a rigidification of $E$ relative to $A_0$ and $\psi$, consisting of curves $E_b, A_b$ over $B/(\pi)$ pulled back from $E$ and from $A_0$ along $\bar\psi =$ `residueLeg`, together with comparison maps $g_b, g_A$ and an isogeny pair $\varphi, \varphi'$ of degree $r^d$ between $E_b$ and $A_b$ preserving the level structure. Let $\sigma$ be a pair of power series in two variables over $B/(\pi)$ with zero constant coefficients, and assume $\sigma$ represents $\varphi'$ followed by $g_b$ in the given coordinates: for every commutative ring $B''$ that is an algebra over $B/(\pi)$, over $B$ and over $k_0$ with $\mathrm{algebraMap}\,B\,B''$ factoring through the quotient map and $\mathrm{algebraMap}\,k_0\,B''$ factoring through $\bar\psi$, every ideal $J$ of $B''$ with $J^{m+1} = 0$, every $s : \mathrm{Fin}\,2 \to J$, and every $B/(\pi)$-point $P_A$ of $A_b$ with $P_A$ followed by $g_A$ equal to the morphism underlying $\theta_0(B'')(s)$, the composite of $P_A$ with $\varphi'$ and then $g_b$ is the morphism underlying $\theta(B'')\big(i \mapsto \mathrm{nilEval}\,m\,(\sigma_i)\,s\big)$. The conclusion is that for every $n \in \mathbb N$ the multiplication-by-$n$ series of $X.F$ reduced modulo $\pi$, with $\sigma$ substituted into it, equals $\sigma$ with the multiplication-by-$n$ series of $X_0.F$ pushed along $\bar\psi$ substituted into it; here the multiplication series is `nthSeries`, defined by $[0] = 0$ and $[n+1]_F = F([n]_F, X)$.
--
--   This is the $\Lambda$-equivariance, for integer multiplications, of the pair of power series that represents the quasi-inverse leg of a rigidification in formal coordinates; it says that $\sigma$ is a homomorphism for the multiplication-by-$n$ endomorphisms of the two formal modules. It feeds the lemmas on rigid transport and on Frobenius twists in the Čerednik–Drinfel'd uniformisation layer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hE : E.IsFormalModuleVia coord X θ)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)

    (σ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0)
    (hσ : (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1))
    (n : ℕ) :
    (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries n)).comp σ =
      σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries n)) := by sorry
