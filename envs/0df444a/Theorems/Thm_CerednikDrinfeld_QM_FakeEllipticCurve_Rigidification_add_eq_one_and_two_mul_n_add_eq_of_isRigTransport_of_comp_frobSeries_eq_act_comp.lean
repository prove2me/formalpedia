-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_add_eq_one_and_two_mul_n_add_eq_of_isRigTransport_of_comp_frobSeries_eq_act_comp
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.add_eq_one_and_two_mul_n_add_eq_of_isRigTransport_of_comp_frobSeries_eq_act_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/9dba6c4b-1ed8-5861-8f96-4e27c94183ee
-- title:
--   Complementary parities and exponent shift for Frobenius-twisted transports
-- statement:
--   The ambient data are: primes $r$ and $\bar r$ with $\bar r\neq r$, a positive integer $N$ with $r\nmid N$; a characteristic-zero discrete valuation domain $\mathcal O$ with irreducible element $\pi$, $\pi$-adically complete, with residue ring of cardinality $r$ and $(r)=(\pi)$, and fraction field $K_0$; a characteristic-zero $\mathcal O$-algebra domain $Onr$ with an $\mathcal O$-automorphism $Fr$, complete for $(\pi)$, with $(\pi)$ maximal, every element integral mod $\pi$ over $\mathcal O$, every monic polynomial of positive degree having a root mod $\pi$, and $Fr(x)\equiv x^{r}$ mod $\pi$; a quaternion algebra $\mathbb H[\mathbb Q,a,b]$ indefinite and ramified exactly at $r,\bar r$, a maximal order $\Lambda$ containing $\mathbb Z$ with an order coordinate `coord` to $\mathrm{Zp2}\,r\times\mathrm{Zp2}\,r$; a fake elliptic curve $A_0$ over $Onr/(\pi)$ which is a formal module via `coord` for a height-$4$ formal $\mathcal O_D$-module $X_0$ with coordinates $\theta_0$; a ring map $\iota:\mathrm{Zp2}\,r\to Onr$, a special formal $\mathcal O_D$-module $\Phi$ of height $4$ over $Onr/(r)$; a moduli package $M$ which is a Zariski sheaf together with $\eta$ sending rigidified objects to points of $M$ and satisfying the three properties of injectivity up to isomorphism on admissible objects, compatibility with base change, and local surjectivity; an injective ring map $E_0$ from the centralizer of the $\mathrm{Zp2}\,r$-action and $\varpi$ on $\Phi$ into $M_2(K_0)$, commensurable with $M_2(\mathcal O)$ up to a power of $r$; a reduction map $\kappa$ from $Onr/(\pi)$ to $Onr/(r)$ compatible with the quotient maps; and an isogeny $\beta_0$ of height $4n_0$ from $\Phi$ to $X_0$ base-changed along $\kappa$ (these are summarised here as the Čerednik–Drinfeld frame). Over a nontrivial Noetherian $\mathcal O$-algebra $B$ in which $\pi$ and $r$ are nilpotent, with $\psi:Onr\to_{\mathcal O} B$, let $x$ be a rigidified curve, and let $X,\theta$ exhibit its underlying fake elliptic curve as a formal module via `coord`. Assume $j\le 1$ and $t$ a rigidified object with $t.X=X$, all constant coefficients of $t.\rho$ zero, which is a rigidification transport of $x$ at level $j$ (so $t.\rho$ factors as the transported series composed with $\beta_0$ and with $X_i\mapsto X_i^{r^{j}}$) and is admissible for some $\chi$; likewise $j'\le 1$ and $t''$ a transport at level $j'$ with $t''.X=X$ and vanishing constant coefficients; and $t'$ a rigidified object with $t'.X=X$, admissible for some $\chi'$, such that substituting $X_i\mapsto X_i^{r}$ into $t'.\rho$ equals the $r$-multiplication of $t''.\bar X$ applied after $t''.\rho$. The conclusion is $j+j'=1$ and $2\,t'.n+j=2\,t.n+j'+1$.
--
--   This is the height (kernel-degree) bookkeeping step in the supersingular dictionary of the Čerednik–Drinfeld uniformisation: two transports of the same rigidification whose series differ by the relative Frobenius have complementary parities $j,j'$, and the associated exponents $n$ shift accordingly, so that $(j,j')=(0,1)$ with $t'.n=t.n+1$, or $(j,j')=(1,0)$ with $t'.n=t.n$. It is used in the comparison of the exponent $n$ across a Frobenius re-basing and in the construction of the scalar action on the rigidified moduli point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_add_eq_one_and_two_mul_n_add_eq_of_isRigTransport_of_comp_frobSeries_eq_act_comp.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.add_eq_one_and_two_mul_n_add_eq_of_isRigTransport_of_comp_frobSeries_eq_act_comp
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

    (B : Type) [CommRing B] [IsNoetherianRing B] [Nontrivial B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (hBr : IsNilpotent ((r : ℕ) : B))
    (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (hX : x.1.IsFormalModuleVia coord X θ)
    (j : ℕ) (hj : j ≤ 1) (t : Rigidified r Φ B) (htX : t.X = X) (ht0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t)
    (χ : Onr →+* B) (hadm : t.IsAdmissible ι χ)
    (j' : ℕ) (hj' : j' ≤ 1) (t'' : Rigidified r Φ B) (ht''X : t''.X = X) (ht''0 : ∀ i, MvPowerSeries.constantCoeff (t''.ρ i) = 0)
    (htr'' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j' t'')
    (t' : Rigidified r Φ B) (ht'X : t'.X = X) (χ' : Onr →+* B) (hadm' : t'.IsAdmissible ι χ')
    (hrel : t'.ρ.comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) 1) = (t''.Xbar.act (r : Zp2 r)).comp t''.ρ) :
    j + j' = 1 ∧ 2 * t'.n + j = 2 * t.n + j' + 1 := by sorry
