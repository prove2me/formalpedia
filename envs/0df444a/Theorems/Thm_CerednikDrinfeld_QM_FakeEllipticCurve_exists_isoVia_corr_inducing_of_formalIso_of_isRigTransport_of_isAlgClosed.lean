-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/a78b3f3d-4a73-5556-96ae-8471d4422fc7
-- title:
--   Formal isomorphism of transported rigidifications descends to the curves
-- statement:
--   Fix primes $r \neq \bar r$ and $N \neq 0$ with $r \nmid N$. Let $\mathcal O$ be a characteristic-zero discrete valuation domain with uniformiser $\pi$, $\pi$-adically complete, with $\#(\mathcal O/\pi) = r$ and $(r) = (\pi)$, and $K_0$ its fraction field; let $Onr$ be a characteristic-zero $\mathcal O$-domain, complete for $(\pi)$, with $(\pi)$ maximal, residually algebraic over $\mathcal O/\pi$, residually closed under monic polynomials, equipped with an $\mathcal O$-automorphism $Fr$ satisfying $Fr(x) \equiv x^r \pmod \pi$. Let $\mathbb H[\mathbb Q,a,b]$ be indefinite and ramified exactly at $r$ and $\bar r$, $\Lambda$ a maximal order containing $\mathbb Z$, and $coord$ an order coordinatisation of $\Lambda$ at $r$ with values in $Zp2\,r \times Zp2\,r$. Further data: a fake elliptic curve $A_0$ over $Onr/\pi$ with formal module $X_0$ of height $4$ in coordinates $\theta_0$; a ring map $\iota : Zp2\,r \to Onr$; a special formal module $\Phi$ of height $4$ over $Onr/r$ whose endomorphism centraliser embeds into $M_2(K_0)$ with image commensurable to $M_2(\mathcal O)$; the comparison map $\kappa : Onr/\pi \to Onr/r$ and an isogeny $\beta_0 : \Phi \to X_0 \otimes_\kappa$ of height $4n_0$. Let $k$ be an algebraically closed $\mathcal O$-algebra in which $\pi$ and $r$ are nilpotent, $\psi : Onr \to k$ an $\mathcal O$-algebra map, and $x = (E,\rho)$, $x' = (E',\rho')$ rigidified fake elliptic curves over $(k,\psi)$ with formal modules $X, X'$ in coordinates $\theta, \theta'$. Let $t = (X,n,\rho_t)$ and $t' = (X',n',\rho_{t'})$ be rigidified objects whose formal modules are $X$ and $X'$, each a rigidity transport of $\rho$, resp. $\rho'$, with the same exponent $j$ relative to $\theta_0, \kappa, \beta_0$, and each admissible for $\iota$ and $\psi \circ Fr^{-j}$. Assume $T_0 : X \to X'$ is an isomorphism of formal $\mathcal O_D$-modules and, for some $m$, that $[r^{m+n'}]$ applied after the reduction of $T_0$ composed with $\rho_t$ equals $[r^{m+n}]$ applied after $\rho_{t'}$, both as series over $k/(r)$ with the action of $\bar X'$. Then there is an isomorphism $i : E.A \cong E'.A$ over $\mathrm{Spec}\,k$ compatible with the group laws, the $\Lambda$-actions and the level structures; for every $k$-algebra $B''$, ideal $J$ with $J^{n+1} = 0$ and $s : \mathrm{Fin}\,2 \to J$, the point $\theta(B'',s)$ followed by $i$ equals $\theta'(B'', \mathrm{nilEval}_n(T_0)(s))$; and there are maps $i_b : E_b.A \to E'_b.A$ over the reduction, compatible with $g_b$ via $i$ and over the base, and $u_A : A'_b.A \to A_b.A$ exhibiting $A'_b$ as a pullback of $A_b$ along the identity and compatible with the maps to $A_0$, together with natural numbers $i_1, j_1$ such that $i_b$ followed by $\varphi'$, then $u_A$, then multiplication by $r^{i_1}$ equals $\varphi$ followed by multiplication by $r^{j_1}$.
--
--   This is the residue-field case of the rigidity half of the Čerednik–Drinfeld dictionary: a formal isomorphism matching the Drinfeld transports of two rigidifications is induced by a genuine isomorphism of the rigidified fake elliptic curves, with the two rigidification data corresponding up to powers of $r$. It is the base step used by the statement over Artinian local rings, which in turn feeds the lifting of isomorphisms along nilpotent ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed
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

    (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (hkr : IsNilpotent ((r : ℕ) : k))
    (ψ : Onr →ₐ[𝒪] k)
    (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ k ψ)
    (X X' : FormalODModule r k)
    (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2)
    (hX : x.1.IsFormalModuleVia coord X θ) (hX' : x'.1.IsFormalModuleVia coord X' θ')

    (j : ℕ) (t t' : Rigidified r Φ k) (htX : t.X = X) (ht'X : t'.X = X')
    (ht : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t)
    (ht' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x'.2 θ' j t')
    (hta : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] k) : Onr →+* k))
    (ht'a : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] k) : Onr →+* k))

    (T₀ : FormalODModule.Hom X X') (hT₀ : T₀.IsIso) (m : ℕ)
    (hTρ : (t'.Xbar.act ((r : Zp2 r) ^ (m + t'.n))).comp
        ((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r k))).comp t.ρ) =
      (t'.Xbar.act ((r : Zp2 r) ^ (m + t.n))).comp t'.ρ) :
    ∃ (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f), FakeEllipticCurve.IsoVia x.1 x'.1 i hi ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ l, s l ∈ J) →
            (θ B'' s).1 ≫ i.hom = (θ' B'' (fun l => MvFormalGroup.nilEval n (T₀.toSeries l) s)).1) ∧

      ∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
        (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
        (i₁ j₁ : ℕ),
        ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
