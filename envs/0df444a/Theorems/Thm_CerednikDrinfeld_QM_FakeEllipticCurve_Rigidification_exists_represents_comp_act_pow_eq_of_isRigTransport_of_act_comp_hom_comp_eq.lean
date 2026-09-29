-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/b39199ae-02b8-5866-a63f-18a7c9fb15cf
-- title:
--   Cancelling the Frobenius leg in an intertwining of transports
-- statement:
--   Fix primes $r$ and $\bar r$ with $\bar r \neq r$, a natural number $N$ not divisible by $r$, a complete discrete valuation ring $\mathcal O$ of characteristic zero with irreducible element $\pi$, residue ring of cardinality $r$ and $(r)=(\pi)$, a fraction field $K_0$ of $\mathcal O$, and an $\mathcal O$-algebra $O^{nr}$ that is a complete domain of characteristic zero with $(\pi)$ maximal, residually algebraic over $\mathcal O$, residually algebraically closed, and carrying an $\mathcal O$-automorphism $F_r$ with $F_r(x)\equiv x^r \pmod \pi$. Further data: rationals $a,b$ with $\mathbb H[\mathbb Q,a,b]$ indefinite and a division algebra exactly at the places above $r$ and $\bar r$; a maximal order $\Lambda$ containing $\mathbb Z$, with order coordinates `coord` into $\mathrm{Zp2}\,r \times \mathrm{Zp2}\,r$; a fake elliptic curve $A_0$ over $O^{nr}/\pi$ with formal coordinates $\theta_0$ realising it as the formal $\mathcal O_D$-module $X_0$ of height $4$ via `coord`; a ring map $\iota : \mathrm{Zp2}\,r \to O^{nr}$; a special formal $\mathcal O_D$-module $\Phi$ of height $4$ over $O^{nr}/r$; an injective ring map $E_0$ from the centralizer of the $\mathrm{Zp2}\,r$-action and $\varpi$ on $\Phi$ into $M_2(K_0)$ whose image is commensurable with $M_2(\mathcal O)$ (up to a fixed power $r^m$ in both directions); a bridge $\kappa : O^{nr}/\pi \to O^{nr}/r$ lifting the quotient maps; and an isogeny $\beta_0 : \Phi \to X_0\otimes_\kappa$ of height $4n_0$. Now let $B$ be an $\mathcal O$-algebra with a leg $\psi : O^{nr} \to B$, let $x=(E,\rho)$ and $x'=(E',\rho')$ be rigidified fake elliptic curves over $(B,\psi)$ relative to $A_0$, let $X, X'$ be formal $\mathcal O_D$-modules over $B$, let $\theta,\theta'$ be formal coordinates for $E$, $E'$, and let $t,t'$ be rigidifications of $\Phi$ over $B$ whose series $t.\rho$, $t'.\rho$ have vanishing constant coefficients and which are rigid transports of $\rho$, $\rho'$ in these coordinates with the same Frobenius exponent $j$. Finally let $T_0 : X \to X'$ be a homomorphism of formal $\mathcal O_D$-modules and $m$ a natural number with $$[r^{\,m+t'.n}]\circ \bar T_0\circ t.\rho = [r^{\,m+t.n}]\circ t'.\rho$$ over $B/r$, the multiplications being taken on $X'\otimes B/r$. The conclusion asserts the existence of a bridge $\kappa_B : B/\pi \to B/r$ lifting the quotient maps and compatible with the two legs (i.e. $\kappa_B \circ \mathrm{residueLeg}\,\pi\,\psi = \mathrm{residueMap}(\psi)\circ\kappa$), of series $\sigma,\sigma'$ over $B/\pi$, and of an exponent $N$, such that: on every ring $B''$ that is simultaneously an algebra over $B$, over $B/\pi$ and over $O^{nr}/\pi$ with the two compatibility identities between the structure maps, for every ideal $J$ with $J^{m+1}=0$ and every tuple $s$ of elements of $J$, each point $P_A$ of $x.2.\mathrm{Ab}$ over $B/\pi$ with $P_A$ followed by $x.2.g_A$ equal to $\theta_0(s)$ satisfies that $P_A$ followed by $x.2.\varphi'$ and $x.2.g_b$ equals $\theta$ evaluated at the truncated substitution of $s$ into $\sigma$, and likewise for $x'$, $\theta'$, $\sigma'$; moreover $t.\rho = \kappa_{B*}\sigma \circ \mathrm{residueMap}(\psi)_*\beta_0 \circ \mathrm{frobSeries}\,j$ and $t'.\rho = \kappa_{B*}\sigma' \circ \mathrm{residueMap}(\psi)_*\beta_0 \circ \mathrm{frobSeries}\,j$, and finally $$[r^{\,m+t'.n}]\circ \bar T_0 \circ \kappa_{B*}\sigma \circ [r^{N}] = [r^{\,m+t.n}]\circ \kappa_{B*}\sigma' \circ [r^{N}],$$ where $[r^N]$ denotes the action of $r^N$ on $X_0$ base changed along $\kappa$ and then along $\mathrm{residueMap}(\psi)$. The exponent $N$ produced here is unrelated to the level $N$ of the moduli data.
--
--   This is the power-series step of the Čerednik–Drinfeld uniformisation argument in which, from an intertwining of two rigid transports over $B/r$, the common right factor $\beta_0 \circ \mathrm{Frob}^j$ is cancelled and replaced by a power of $r$ acting on the formal module of the base curve, leaving an identity between the series $\sigma,\sigma'$ that represent the two quasi-isogenies $A_b \to E_b$, $A_b \to E'_b$ on nilpotent points. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed), so that the scheme-level part of that argument can be carried out separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hX₀ : X₀.HasHeight 4)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ)
    (X X' : FormalODModule r B)
    (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2)
    (j : ℕ) (t t' : Rigidified r Φ B)
    (ht0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0) (ht'0 : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0)
    (ht : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t)
    (ht' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x'.2 θ' j t')

    (T₀ : FormalODModule.Hom X X') (m : ℕ)
    (hTρ : (t'.Xbar.act ((r : Zp2 r) ^ (m + t'.n))).comp
        ((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r B))).comp t.ρ) =
      (t'.Xbar.act ((r : Zp2 r) ^ (m + t.n))).comp t'.ρ) :
    ∃ (κB : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B ⧸ pIdeal r B))
      (σ σ' : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (N : ℕ),

      κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) = Ideal.Quotient.mk (pIdeal r B) ∧
      κB.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) = (residueMap (ψ : Onr →+* B)).comp κ ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
          [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
          algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
          algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
            (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
          ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            ∀ PA : Spec (CommRingCat.of B'') ⟶ x.2.Ab.A,
              PA ≫ x.2.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
              PA ≫ x.2.gA = (θ₀ B'' s).1 →
                PA ≫ x.2.φ' ≫ x.2.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1) ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
          [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
          algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
          algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
            (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
          ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            ∀ PA : Spec (CommRingCat.of B'') ⟶ x'.2.Ab.A,
              PA ≫ x'.2.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
              PA ≫ x'.2.gA = (θ₀ B'' s).1 →
                PA ≫ x'.2.φ' ≫ x'.2.gb = (θ' B'' (fun i => MvFormalGroup.nilEval m (σ' i) s)).1) ∧

      t.ρ = (σ.map κB).comp ((β₀.map (residueMap (ψ : Onr →+* B))).comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j)) ∧
      t'.ρ = (σ'.map κB).comp ((β₀.map (residueMap (ψ : Onr →+* B))).comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j)) ∧

      ((t'.Xbar.act ((r : Zp2 r) ^ (m + t'.n))).comp
          ((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r B))).comp (σ.map κB))).comp
        (((X₀.map κ).map (residueMap (ψ : Onr →+* B))).act ((r : Zp2 r) ^ N)) =
      ((t'.Xbar.act ((r : Zp2 r) ^ (m + t.n))).comp (σ'.map κB)).comp
        (((X₀.map κ).map (residueMap (ψ : Onr →+* B))).act ((r : Zp2 r) ^ N)) := by sorry
