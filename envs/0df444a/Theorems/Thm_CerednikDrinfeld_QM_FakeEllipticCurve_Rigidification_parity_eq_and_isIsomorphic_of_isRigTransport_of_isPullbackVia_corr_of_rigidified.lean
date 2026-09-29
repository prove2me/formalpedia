-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_parity_eq_and_isIsomorphic_of_isRigTransport_of_isPullbackVia_corr_of_rigidified
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.parity_eq_and_isIsomorphic_of_isRigTransport_of_isPullbackVia_corr_of_rigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/6defc5d3-9353-5778-805c-e04a52cf3e8f
-- title:
--   Rigidity of Drinfeld transport along a nilpotent thickening
-- statement:
--   The hypotheses fall into groups, summarised here. Arithmetic base: distinct primes $r,\bar r$, a nonzero $N$ with $r\nmid N$; a characteristic-zero discrete valuation ring $\mathcal O$ with uniformiser $\pi$, $\pi$-adically complete, residue ring of cardinality $r$ and $(r)=(\pi)$, with fraction field $K_0$; a characteristic-zero domain $Onr$ over $\mathcal O$, complete for $(\pi Onr)$ with that ideal maximal, every element satisfying a monic $\mathcal O$-polynomial modulo $\pi$ and every monic polynomial having a root modulo $\pi$, together with an $\mathcal O$-automorphism $Fr$ congruent to $x\mapsto x^r$ modulo $\pi$. Quaternionic data: $a,b\in\mathbb Q$ with $\mathbb H[\mathbb Q,a,b]$ indefinite and ramified exactly at $r$ and $\bar r$, a maximal order $\Lambda$ containing the integers, and order coordinates $coord:\Lambda\to \mathrm{Zp2}\,r\times \mathrm{Zp2}\,r$ satisfying `IsOrderCoord`. Base point: a fake elliptic curve $A_0$ over $Onr/\pi$ whose formal group is given, via $coord$, by a formal $\mathcal O_D$-module $X_0$ of height $4$ with coordinates $\theta_0$. Drinfeld datum: $\iota:\mathrm{Zp2}\,r\to Onr$, a special formal $\mathcal O_D$-module $\Phi$ of height $4$ over $Onr/(r)$, a moduli package $M$ satisfying the Zariski sheaf condition, a family $\eta$ sending rigidified objects to points of $M$ and obeying the three laws (admissible objects over Noetherian rings have equal $\eta$-values exactly when isomorphic; $\eta$ commutes with base change; every point of $M$ is, Zariski-locally on a finite covering by localisations, of the form $\eta(t)$ for admissible $t$), and an injective homomorphism $E_0$ from the centraliser of $\Phi$'s $\mathrm{Zp2}\,r$-action and $\varpi$-endomorphism into $M_2(K_0)$ whose image agrees with $M_2(\mathcal O)$ up to a fixed power $r^m$ in both directions. Bridge: a ring map $\kappa:Onr/\pi\to Onr/(r)$ compatible with the quotient maps, and a series $\beta_0$ which is an isogeny $\Phi\to X_0\otimes_\kappa Onr/(r)$ of height $4n_0$. Thickening: a Noetherian $\mathcal O$-algebra $A$ and a field $k_A$ over $\mathcal O$, in both of which $\pi$ and $r$ are nilpotent, a surjective $\mathcal O$-algebra map $q_\kappa:A\to k_A$ with nilpotent kernel, and $\psi:Onr\to A$. Over $k_A$: a rigidified curve $x_0=(x_0.1,x_0.2)$ for $q_\kappa\circ\psi$, whose formal module is $X_{0\kappa}$ with coordinates $\theta_{0\kappa}$; a parity $j_0\le 1$ and a rigidified object $t_0$ over $k_A$ with $t_0.X=X_{0\kappa}$, which is a transport (`IsRigTransport`) of the rigidification $x_0.2$ in the coordinates $\theta_{0\kappa}$ with parity $j_0$, and is admissible for $\iota$ and the $(-j_0)$-fold $Fr$-twist of $q_\kappa\circ\psi$. Over $A$: a rigidified object $t$, admissible for the $(-j_0)$-twist of $\psi$, together with series $u_0,v_0$ over $k_A$ and $m_0\in\mathbb N$ exhibiting mutually inverse $\mathcal O_D$-homomorphisms between $t_0.X$ and $(t\otimes_{q_\kappa}k_A).X$ whose effect on the $\rho$-data satisfies the stated $r$-power compatibility; a fake elliptic curve $E$ over $A$ with $g:x_0.1.A\to E.A$ making $x_0.1$ the pullback of $E$ along $q_\kappa$; coordinates $\theta$ presenting $E$ as a formal module for $t.X$ via $coord$, coordinates $\theta_t$ presenting $x_0.1$ as a formal module for $t.X\otimes_{q_\kappa}k_A$, with $\theta_t$ followed by $g$ equal to $\theta$ on nilpotent arguments and $\theta_t$ equal to $\theta_{0\kappa}$ reparametrised by the truncated evaluations of $v_0$; a rigidification $\rho$ of $E$ for $\psi$ and a rigidification $\rho'$ of $x_0.1$ for $q_\kappa\circ\psi$ with $\rho'$ the pullback of $\rho$ along $q_\kappa$ compatibly with $g$; maps $ib$ and $uA'$ comparing $x_0.2$ with $\rho'$ (the latter a pullback along the identity) and exponents $i_1,j_1$ with $ib\circ$-composite of $\rho'.\varphi$ and $uA'$ followed by multiplication by $r^{i_1}$ equal to $x_0.2.\varphi$ followed by multiplication by $r^{j_1}$. Finally, let $j\le 1$ and let $t''$ be a rigidified object over $A$ with $t''.X=t.X$, a transport of $\rho$ in the coordinates $\theta$ with parity $j$, admissible for the $(-j)$-twist of $\psi$. The conclusion is that $j=j_0$ and that $t''$ and $t$ are isomorphic as rigidified objects, that is, there are mutually inverse $\mathcal O_D$-isomorphisms between $t''.X$ and $t.X$ and an exponent making the associated $\rho$-series agree after acting by the corresponding power of $r$.
--
--   This is the rigidity (uniqueness) half of the Drinfeld-transport dictionary in the Čerednik–Drinfeld comparison: along a surjection with nilpotent kernel onto a field, a transported rigidified special formal module over the thickening is determined, up to isomorphism and with its parity, by the data downstairs. It is used in the construction of lifts of rigidified fake elliptic curves over Artinian bases, [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedCurve_lift_of_isArtinianRing`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedCurve_lift_of_isArtinianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_parity_eq_and_isIsomorphic_of_isRigTransport_of_isPullbackVia_corr_of_rigidified.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.parity_eq_and_isIsomorphic_of_isRigTransport_of_isPullbackVia_corr_of_rigidified
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
    (M : ModuliPackage.{0, 0} r Onr) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (A : Type) [CommRing A] [IsNoetherianRing A] [Algebra 𝒪 A] (hA : IsNilpotent (algebraMap 𝒪 A π)) (hAr : IsNilpotent ((r : ℕ) : A))
    (kA : Type) [Field kA] [Algebra 𝒪 kA] (hkA : IsNilpotent (algebraMap 𝒪 kA π)) (hkAr : IsNilpotent ((r : ℕ) : kA))
    (qκ : A →ₐ[𝒪] kA) (hqκ : Function.Surjective qκ) (hqn : IsNilpotent (RingHom.ker (qκ : A →+* kA))) (ψ : Onr →ₐ[𝒪] A)
    (x₀ : FakeEllipticCurve.RigidifiedCurve r π A₀ kA (qκ.comp ψ))
    (X₀κ : FormalODModule r kA) (θ₀κ : RelativeGroupLaw.FormalCoordinates x₀.1.f 2) (hx₀ : x₀.1.IsFormalModuleVia coord X₀κ θ₀κ)
    (j₀ : ℕ) (t₀ : Rigidified r Φ kA) (hj₀ : j₀ ≤ 1) (ht₀X : t₀.X = X₀κ)
    (htr₀ : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x₀.2 θ₀κ j₀ t₀)
    (hadm₀ : t₀.IsAdmissible ι ((frobTwist Onr Fr (-(j₀ : ℤ)) (qκ.comp ψ) : Onr →ₐ[𝒪] kA) : Onr →+* kA))

    (t : Rigidified r Φ A) (htadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j₀ : ℤ)) ψ : Onr →ₐ[𝒪] A) : Onr →+* A))
    (u₀ v₀ : Series kA) (m₀ : ℕ)
    (hu₀ : FormalODModule.IsODHom t₀.X (t.map (qκ : A →+* kA)).X u₀) (hv₀ : FormalODModule.IsODHom (t.map (qκ : A →+* kA)).X t₀.X v₀)
    (hvu₀ : v₀.comp u₀ = Series.id kA) (huv₀ : u₀.comp v₀ = Series.id kA)
    (hc₀ : ((t.map (qκ : A →+* kA)).Xbar.act ((r : Zp2 r) ^ (m₀ + (t.map (qκ : A →+* kA)).n))).comp
        ((u₀.map (Ideal.Quotient.mk (pIdeal r kA))).comp t₀.ρ)
      = ((t.map (qκ : A →+* kA)).Xbar.act ((r : Zp2 r) ^ (m₀ + t₀.n))).comp (t.map (qκ : A →+* kA)).ρ)

    (E : FakeEllipticCurve Λ N A) (g : x₀.1.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (qκ : A →+* kA) E x₀.1 g)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hEX : E.IsFormalModuleVia coord t.X θ)
    (θt : RelativeGroupLaw.FormalCoordinates x₀.1.f 2) (hEθt : x₀.1.IsFormalModuleVia coord (t.X.map (qκ : A →+* kA)) θt)
    (hθg : ∀ (B'' : Type) [CommRing B''] [Algebra A B''] [Algebra kA B''],
      algebraMap A B'' = (algebraMap kA B'').comp (qκ : A →+* kA) →
      ∀ s : Fin 2 → B'', (∀ i, IsNilpotent (s i)) → (θt B'' s).1 ≫ g = (θ B'' s).1)
    (hθtw : ∀ (B'' : Type) [CommRing B''] [Algebra kA B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) → θt B'' s = θ₀κ B'' (fun i => MvFormalGroup.nilEval n (v₀ i) s))

    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (qκ.comp ψ) x₀.1)
    (hρρ' : FakeEllipticCurve.Rigidification.IsPullbackVia qκ g hgE ρ ρ')
    (ib : x₀.2.Eb.A ⟶ ρ'.Eb.A) (hib₁ : ib ≫ ρ'.gb = x₀.2.gb ≫ (Iso.refl x₀.1.A).hom) (hib₂ : ib ≫ ρ'.Eb.f = x₀.2.Eb.f)
    (uA' : ρ'.Ab.A ⟶ x₀.2.Ab.A) (huA'₁ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x₀.2.Ab ρ'.Ab uA') (huA'₂ : uA' ≫ x₀.2.gA = ρ'.gA)
    (i₁ j₁ : ℕ)
    (hrel : ib ≫ ρ'.φ ≫ uA' ≫ x₀.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x₀.2.φ ≫ x₀.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (j : ℕ) (t'' : Rigidified r Φ A) (hj : j ≤ 1) (ht''X : t''.X = t.X)
    (htr'' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j t'')
    (hadm'' : t''.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] A) : Onr →+* A)) :
    j = j₀ ∧ t''.IsIsomorphic t := by sorry
