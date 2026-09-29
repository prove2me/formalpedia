-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_series_comp_eq_act_pow_and_comp_eq_act_pow_of_isODHom_of_represents
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_series_comp_eq_act_pow_and_comp_eq_act_pow_of_isODHom_of_represents
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/3fef3751-39e1-5a03-ad00-dc7d1e16fa5b
-- title:
--   Quasi-inverse leg of a rigidification in formal coordinates
-- statement:
--   Fix primes $r \ne \bar r$ and a level $N$ with $r \nmid N$. The ambient data are: a complete discrete valuation ring $\mathcal O$ of characteristic $0$ with irreducible element $\pi$, residue ring of cardinality $r$ and $(r) = (\pi)$, with fraction field $K_0$; a $\pi$-adically complete $\mathcal O$-algebra $Onr$, a domain of characteristic $0$, with $(\pi)$ maximal, residually algebraic and residually closed under monic polynomials, together with an automorphism $Fr$ lifting the $r$-power map modulo $\pi$; a quaternion algebra $\mathbb H[\mathbb Q,a,b]$ which is indefinite and exactly ramified at $r$ and $\bar r$, a maximal order $\Lambda$ containing $\mathbb Z$, and a coordinate map `coord` on $\Lambda$ satisfying `IsOrderCoord`; over the residue ring $\bar{Onr} = Onr/(\pi)$ a fake elliptic curve $A_0$ with formal coordinates $\theta_0$ exhibiting a formal $\mathcal O_D$-module $X_0$ of height $4$; a special formal module $\Phi$ of height $4$ over $Onr/(r)$ with structure map through $\iota : \mathbb Z_{r^2} \to Onr$; a moduli package $M$ which is a Zariski sheaf, a family $\eta$ of maps from rigidified objects to $M$ satisfying the three conditions (injectivity up to isomorphism on admissible objects, naturality, local surjectivity), an embedding $E_0$ of the centraliser of the $\mathbb Z_{r^2}$-action and $\varpi$ on $\Phi$ into $M_2(K_0)$ which is injective and has image commensurable to $M_2(\mathcal O)$ with factor $r^m$, a map $\kappa$ compatible with the two quotient maps, and an isogeny $\beta_0 : \Phi \to X_0 \otimes \kappa$ of height $4n_0$; these form the standard frame and are summarised here. Over a Noetherian $\mathcal O$-algebra $B$ with trivial idempotents in which $\pi$ and $r$ are nilpotent, given an $\mathcal O$-algebra map $\psi : Onr \to B$, a fake elliptic curve $E/B$ with a rigidification $\rho$ (giving reductions $E_b, A_b$ over $\bar B = B/(\pi)$, maps $g_b, g_A$, and an isogeny pair $\rho.\varphi, \rho.\varphi'$ of degree $r^{\rho.d}$), and formal coordinates $\theta$ exhibiting a formal $\mathcal O_D$-module $X$ over $B$: suppose $\sigma$ is a pair of power series over $\bar B$ which is a homomorphism of formal $\mathcal O_D$-modules from $X_0$ base changed along `residueLeg` $\pi\,\psi$ to $X$ reduced mod $\pi$ (that is, a homomorphism of the formal group laws commuting with all $\mathbb Z_{r^2}$-actions and with $\varpi$), and suppose $\sigma$ represents the leg $\rho.\varphi'$ followed by $\rho.g_b$ in the sense of `hrep`: for every commutative ring $B''$ which is simultaneously an algebra over $\bar B$, over $B$ and over $\bar{Onr}$ with the two compatibility identities for the structure maps, every ideal $J$ with $J^{m+1} = 0$, every $s : \mathrm{Fin}\,2 \to J$ and every $PA : \operatorname{Spec} B'' \to \rho.A_b$ lying over $\operatorname{Spec}$ of $\bar B \to B''$ with $PA$ followed by $\rho.g_A$ equal to the point $\theta_0(B'')(s)$, one has that $PA$ followed by $\rho.\varphi'$ and then $\rho.g_b$ equals $\theta(B'')$ evaluated at the truncated substitutions $\mathrm{nilEval}\,m\,(\sigma_i)\,s$. Then there exists a pair of power series $\tau$ over $\bar B$ with zero constant coefficients which is a homomorphism of formal $\mathcal O_D$-modules in the opposite direction, from $X$ reduced mod $\pi$ to $X_0$ base changed along `residueLeg` $\pi\,\psi$, such that $\tau \circ \sigma$ is the action of $r^{\rho.d} \in \mathbb Z_{r^2}$ on the first module and $\sigma \circ \tau$ is the action of $r^{\rho.d}$ on the second.
--
--   This is the step in the Čerednik–Drinfeld comparison which shows that both legs of the isogeny pair underlying a rigidification are visible in formal coordinates: the leg $\rho.\varphi$ gives a power-series quasi-inverse to $\sigma$, the two compositions being multiplication by $r^{\rho.d}$ on the two formal $\mathcal O_D$-modules. It is used to compute the kernel degree of $\sigma$, in [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_hasKernelOfDegree_pow_two_mul_of_isODHom_of_represents`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_hasKernelOfDegree_pow_two_mul_of_isODHom_of_represents).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_series_comp_eq_act_pow_and_comp_eq_act_pow_of_isODHom_of_represents.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_series_comp_eq_act_pow_and_comp_eq_act_pow_of_isODHom_of_represents
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

    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hBr : IsNilpotent ((r : ℕ) : B))
    (E : FakeEllipticCurve Λ N B) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)

    (σ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (hσ : FormalODModule.IsODHom (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ))
      (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) σ)
    (hrep : ∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1) :
    ∃ τ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}),
      (∀ i, MvPowerSeries.constantCoeff (τ i) = 0) ∧
      FormalODModule.IsODHom (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})))
        (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) τ ∧
      τ.comp σ = (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ ρ.d) ∧
      σ.comp τ = (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act ((r : Zp2 r) ^ ρ.d) := by sorry
