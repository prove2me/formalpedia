-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidifiedCurve_isRigTransport_zero_isIsomorphic_of_quotient_of_isFormalModuleVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedCurve_isRigTransport_zero_isIsomorphic_of_quotient_of_isFormalModuleVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/e7698615-c865-5f0d-8a63-15099df99c26
-- title:
--   Rigidified curve realising a given admissible rigidified formal module
-- statement:
--   Fix primes $r$, $\bar r$ with $\bar r \neq r$ and a nonzero $N$ with $r \nmid N$. The coefficients consist of: a characteristic-zero discrete valuation domain $\mathcal{O}$ with irreducible element $\pi$, $\pi$-adically complete, with residue ring of cardinality $r$ and $(r) = (\pi)$, together with a fraction field $K_0$; an $\mathcal{O}$-algebra $Onr$ which is a characteristic-zero domain, complete for $(\pi)$, with $(\pi)$ maximal, every element a root mod $\pi$ of a monic polynomial over $\mathcal{O}$, every monic polynomial of positive degree over $Onr$ having a root mod $\pi$, and an $\mathcal{O}$-algebra automorphism $F_r$ with $F_r x \equiv x^r \pmod \pi$; a quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ with $0<a$ or $0<b$ whose completion at a finite place is a division algebra exactly at the places above $r$ and $\bar r$, a maximal order $\Lambda$ containing the rational integers, and an injective, additive, suitably twisted-multiplicative coordinate map $\mathrm{coord} : \Lambda \to \mathrm{Zp2}\,r \times \mathrm{Zp2}\,r$ with dense image, unit and trace normalisations. Over the residue ring $Onr/(\pi)$ one is given a fake elliptic curve $A_0$ for $(\Lambda,N)$, a formal $\mathcal{O}_D$-module $X_0$ of height $4$ (multiplication by $r$ has kernel of degree $r^4$), and formal coordinates $\theta_0$ of the relative group law of $A_0$ exhibiting $A_0$ as a formal module for $X_0$ via $\mathrm{coord}$. Over $Onr/(r)$ one is given $\iota : \mathrm{Zp2}\,r \to Onr$, a special formal $\mathcal{O}_D$-module $\Phi$ of height $4$ for the reduction of $\iota$, and an injective ring homomorphism $E_0$ from the centraliser of the $\mathrm{Zp2}\,r$-action and $\varpi$ on $\Phi$ into $M_2(K_0)$ whose image is commensurable with $M_2(\mathcal{O})$ in the precise sense that for some $m$ every $r^m A$ with $A$ over $\mathcal{O}$ is in the image and $r^m E_0(e)$ always lies in $M_2(\mathcal{O})$. Further: a ring map $\kappa : Onr/(\pi) \to Onr/(r)$ compatible with the quotient maps, and a series $\beta_0$ which is an isogeny $\Phi \to X_0 \otimes_\kappa$ of height $4 n_0$. Over an algebraically closed $\mathcal{O}$-field $k$ in which $\pi$ and $r$ are nilpotent, one is given $\psi : Onr \to k$, a rigidified datum $t = (X_t, n_t, \rho_t)$ over $k$ admissible for $\iota$ and $\psi$ (so $X_t$ is special of height $4$ and $\rho_t$ is an isogeny of height $4 n_t$ from the reduction of $\Phi$ to $\bar X_t$), the induced $\psi_b : Onr/(\pi) \to k$, a fake elliptic curve $A$ over $k$ pulling back $A_0$ along $\psi_b$ via $g_{A_0}$, formal coordinates $\theta_A$ exhibiting $A$ as a formal module for $X_0 \otimes_{\psi_b}$ whose composition with $g_{A_0}$ is $\theta_0$, a fake elliptic curve $E$ over $k$ with morphisms $p$, $p'$ over $\operatorname{Spec} k$ forming an $r^c$-isogeny pair with $A$ and with $p'$ preserving level, formal coordinates $\theta_E$ exhibiting $E$ as a formal module for $X_t$, an $\mathcal{O}_D$-module homomorphism $\gamma_p : X_0 \otimes_{\psi_b} \to X_t$ whose truncated evaluations compute $\theta_A$ followed by $p$ in terms of $\theta_E$, and an exponent $e$ with $(\gamma_p \bmod r) \circ (\beta_0 \text{ along } \psi) = \bar X_t$-multiplication by $r^e$ composed with $\rho_t$. The conclusion asserts the existence of a pair $x$ consisting of a fake elliptic curve over $k$ together with a rigidification of it relative to $A_0$, $\pi$ and $\psi$ (reductions mod $\pi$ of the curve and of $A_0$, linked by an $r^d$-isogeny pair preserving level), a formal $\mathcal{O}_D$-module $X$ over $k$, formal coordinates $\theta$ for the curve underlying $x$, and a rigidified datum $t'$ over $k$, such that $x$'s curve is a formal module for $X$ via $\mathrm{coord}$ and $\theta$, $t'.X = X$, $t'$ is the transport of the rigidification of $x$ with respect to $\theta_0$, $\kappa$, $\beta_0$, $\theta$ with substitution exponent $0$, $t'$ is admissible for $\iota$ and $\psi$, and $t'$ is isomorphic to $t$.
--
--   This is the assembly step in the Čerednik–Drinfeld strand: it converts the analytic data attached to the quotient curve (the isogeny pair $p$, $p'$ over the algebraically closed base, together with the formal coordinates and the series $\gamma_p$) into an honest rigidified fake elliptic curve whose associated rigidified formal $\mathcal{O}_D$-module reproduces the given admissible datum $t$ up to isomorphism, with transport exponent $0$. It is used by the corresponding statement for admissible data over an algebraically closed base, from which the comparison with the special formal moduli problem is obtained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidifiedCurve_isRigTransport_zero_isIsomorphic_of_quotient_of_isFormalModuleVia.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedCurve_isRigTransport_zero_isIsomorphic_of_quotient_of_isFormalModuleVia
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
    (ψ : Onr →ₐ[𝒪] k) (t : Rigidified r Φ k) (ht : t.IsAdmissible ι ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k))

    (ψb : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* k)
    (hψb : ψb.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k))
    (A : FakeEllipticCurve Λ N k) (gA₀ : A.A ⟶ A₀.A) (hA : FakeEllipticCurve.IsPullbackVia ψb A₀ A gA₀)
    (θA : RelativeGroupLaw.FormalCoordinates A.f 2) (hXA : A.IsFormalModuleVia coord (X₀.map ψb) θA)
    (hθA : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
      algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap k B'').comp ψb →
      ∀ s : Fin 2 → B'', (∀ i, IsNilpotent (s i)) → (θA B'' s).1 ≫ gA₀ = (θ₀ B'' s).1)

    (E : FakeEllipticCurve Λ N k) (p : A.A ⟶ E.A) (hp : p ≫ E.f = A.f) (p' : E.A ⟶ A.A) (hp' : p' ≫ A.f = E.f)
    (c : ℕ) (hpair : FakeEllipticCurve.IsIsogenyPair (r ^ c) A E p p')
    (hlev : FakeEllipticCurve.PreservesLevel E A p' hp')

    (θE : RelativeGroupLaw.FormalCoordinates E.f 2) (hXE : E.IsFormalModuleVia coord t.X θE)
    (γp : Series k) (hγp : FormalODModule.IsODHom (X₀.map ψb) t.X γp)
    (hγp_germ : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (θA B'' s).1 ≫ p = (θE B'' (fun i => MvFormalGroup.nilEval n (γp i) s)).1)
    (e : ℕ)
    (hγρ : (γp.map (Ideal.Quotient.mk (pIdeal r k))).comp (β₀.map (residueMap ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k))) =
      (t.Xbar.act ((r : Zp2 r) ^ e)).comp t.ρ) :
    ∃ (x : FakeEllipticCurve.RigidifiedCurve r π A₀ k ψ) (X : FormalODModule r k) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2)
      (t' : Rigidified r Φ k),
      x.1.IsFormalModuleVia coord X θ ∧ t'.X = X ∧
      FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ 0 t' ∧
      t'.IsAdmissible ι ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k) ∧ t'.IsIsomorphic t := by sorry
