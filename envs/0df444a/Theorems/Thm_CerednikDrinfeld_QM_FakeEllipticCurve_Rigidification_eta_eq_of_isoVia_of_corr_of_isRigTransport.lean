-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_eta_eq_of_isoVia_of_corr_of_isRigTransport
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.eta_eq_of_isoVia_of_corr_of_isRigTransport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/4b848be0-51de-5d7a-b888-cef1b10945b9
-- title:
--   Corresponding rigidifications transport to the same η-point
-- statement:
--   Fix primes $r \neq \bar r$ and $N \neq 0$ with $r \nmid N$; a complete discrete valuation domain $\mathcal{O}$ of characteristic zero with uniformiser $\pi$, residue cardinality $r$ and $(r)=(\pi)$, with fraction field $K_0$; and a characteristic-zero domain $\mathcal{O}^{nr}$ over $\mathcal{O}$ with an $\mathcal{O}$-automorphism $Fr$, $\pi$-adically complete, $(\pi)$ maximal, every element integral modulo $\pi$, every monic polynomial of positive degree having a root modulo $\pi$, and $Fr(x) \equiv x^{r} \pmod{\pi}$. Further data: rationals $a,b$ with $\mathbb{H}[\mathbb{Q},a,b]$ indefinite and ramified exactly at $r$ and $\bar r$; a maximal order $\Lambda$ containing $\mathbb{Z}$ with an order coordinate $\mathrm{coord}$ into $\mathbb{Z}_{r^2} \times \mathbb{Z}_{r^2}$; a fake elliptic curve $A_0$ over $\mathcal{O}^{nr}/\pi$ with formal module $X_0$ of height $4$ and coordinates $\theta_0$; a ring map $\iota : \mathbb{Z}_{r^2} \to \mathcal{O}^{nr}$ and a special formal $\mathcal{O}_D$-module $\Phi$ of height $4$ over $\mathcal{O}^{nr}/r$; a moduli package $M$ that is a Zariski sheaf together with $\eta$ sending rigidified objects to points of $M$, subject to the three clauses of $h\eta$ (it separates precisely the isomorphism classes of admissible rigidified objects, commutes with base change, and is Zariski-locally surjective); an injective map $E_0$ of the centraliser of the $\Phi$-endomorphisms into $M_2(K_0)$ with the stated $r$-power integrality; a reduction $\kappa$ and an isogeny $\beta_0 : \Phi \to X_0 \otimes \kappa$ of height $4n_0$. Over a nonzero Noetherian $\mathcal{O}$-algebra $B$ with $\pi$ and $r$ nilpotent and a leg $\psi : \mathcal{O}^{nr} \to B$, let $i : E \cong E'$ be an isomorphism of fake elliptic curves over $B$ compatible with group law, $\Lambda$-action and level, let $\varrho,\varrho'$ be rigidifications of $E,E'$, and let $i_b$, $u_A$ (a pullback along the identity) and exponents $i_1,j_1$ satisfy the compatibilities $i_b \circ \varrho'.g_b$ type relations and $\varrho.\mathrm{act}(r^{i_1}) \circ u_A \circ \varrho'.\varphi \circ i_b = \varrho.\mathrm{act}(r^{j_1}) \circ \varrho.\varphi$ in diagrammatic order. Let $(X,\theta,j,t)$ and $(X',\theta',j',t')$ be rig-transports of $\varrho$ and $\varrho'$ with $j,j' \le 1$, $t.X = X$, $t'.X = X'$, each admissible with respect to $\iota$ and the Frobenius twist of $\psi$ by $-j$, resp. $-j'$. Then $j' = j$, $t'.n + \varrho.d + j_1 = t.n + \varrho'.d + i_1$, and $\eta$ takes the same value on $t'$ and $t$ at the twist by $-j$.
--
--   This is the well-definedness step in the Čerednik–Drinfeld comparison: the point of the moduli package attached to a fake elliptic curve with rigidification, via a transport of formal coordinates, depends only on the isomorphism class of the curve and not on the chosen rigidification or transport, and the associated Frobenius-twist exponent and rigidification degree are rigid. It feeds the constructions of the $G$-point attached to a rigidification and of the full-level norm transport.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_eta_eq_of_isoVia_of_corr_of_isRigTransport.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.eta_eq_of_isoVia_of_corr_of_isRigTransport
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
    (E E' : FakeEllipticCurve Λ N B) (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hiso : FakeEllipticCurve.IsoVia E E' i hi)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hibg : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ϱ θ j t) (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    (X' : FormalODModule r B) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2) (hX' : E'.IsFormalModuleVia coord X' θ')
    (j' : ℕ) (t' : Rigidified r Φ B) (hj' : j' ≤ 1) (ht'X : t'.X = X')
    (htr' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ϱ' θ' j' t') (hadm' : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j' : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    :
    j' = j ∧ t'.n + ϱ.d + j₁ = t.n + ϱ'.d + i₁ ∧ η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t' = η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t := by sorry
