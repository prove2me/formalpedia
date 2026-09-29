-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_parity_eq_and_n_eq_and_act_pow_comp_eq_of_isoVia_of_corr_of_isRigTransport_of_isFormalCompletionAlong
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.parity_eq_and_n_eq_and_act_pow_comp_eq_of_isoVia_of_corr_of_isRigTransport_of_isFormalCompletionAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/7ca84404-a79f-5d3f-a847-f5b144cad348
-- title:
--   Corresponding rigidifications: equal parity, exponents and transported series
-- statement:
--   Fix distinct primes $r$ and $\bar r$ with $r\nmid N$. The arithmetic input, summarised here, consists of: a complete discrete valuation ring $\mathcal O$ of characteristic zero with uniformiser $\pi$, residue cardinality $r$ and $(r)=(\pi)$, with fraction field $K_0$; an $\mathcal O$-algebra $Onr$ that is $\pi$-adically complete with maximal ideal $(\pi)$, integral over $\mathcal O$ and residually algebraically closed, carrying an automorphism $Fr$ lifting the $r$-power map modulo $\pi$; a quaternion algebra $\mathbb H[\mathbb Q,a,b]$ indefinite and ramified exactly at $r$ and $\bar r$, a maximal order $\Lambda$ containing $\mathbb Z$ with order coordinates $coord$; a fake elliptic curve $A_0$ over $Onr/(\pi)$ with formal module $(X_0,\theta_0)$ of height $4$; a special formal $\mathcal O_D$-module $\Phi$ over $Onr/(r)$ of height $4$; a Zariski-sheaf moduli package $M$ together with $\eta$ sending rigidified objects to points of $M$ and separating admissible objects exactly up to isomorphism, natural in the base and locally surjective; an injective map $E_0$ of the centraliser of the $\Phi$-action into $M_2(K_0)$ commensurable with $M_2(\mathcal O)$; a comparison $\kappa$ of the two quotients and an isogeny $\beta_0$ from $\Phi$ to $X_0$ pushed along $\kappa$ of height $4n_0$. Over a nontrivial Noetherian $\mathcal O$-algebra $B$ in which $\pi$ and $r$ are nilpotent, with $\psi:Onr\to B$, let $i$ be an isomorphism $E\cong E'$ of fake elliptic curves over $B$ compatible with the structure morphisms, with the group laws, the $\Lambda$-actions and the level structures (`IsoVia`), let $\varrho$, $\varrho'$ be rigidifications of $E$, $E'$, and let $ib$, $uA$ be morphisms of their reductions compatible with $gb$, $i$ and with $gA$, $uA$ exhibiting $\varrho'.Ab$ as a pullback of $\varrho.Ab$ along the identity, such that $ib$ followed by $\varrho'.\varphi$, $uA$ and $[r^{i_1}]$ equals $\varrho.\varphi$ followed by $[r^{j_1}]$. Let $(X,\theta)$ and $(X',\theta')$ be formal $\mathcal O_D$-module structures on $E$, $E'$ via $coord$, and $j,j'\le 1$, $t,t'$ rigidified objects with $t.X=X$, $t'.X=X'$, which are rigidification transports (`IsRigTransport`) of $\varrho$, $\varrho'$ with parities $j$, $j'$ and are admissible for the legs twisted by $Fr^{-j}$, $Fr^{-j'}$. Finally let $v$ be a homomorphism of formal $\mathcal O_D$-modules $X'\to X$ which is the formal completion of $i^{-1}$ along $\theta'$, $\theta$. Then $j'=j$; $t'.n+\varrho.d+j_1=t.n+\varrho'.d+i_1$; $\eta(t')=\eta(t)$ for the leg twisted by $Fr^{-j}$; and, after reduction to $B/rB$, the series identity $[r^{\varrho.d+j_1+1}]\circ \bar v\circ t'.\rho=[r^{\varrho'.d+i_1+1}]\circ t.\rho$ holds, the multiplications being by powers of $r$ in the $\mathcal O_D$-action on $X$ reduced modulo $r$.
--
--   This is the compatibility of rigidifications of fake elliptic curves under an isomorphism of the curves, in the form used in the Čerednik–Drinfeld uniformisation of Shimura curves: corresponding rigidifications have the same parity, matching exponents, the same image under $\eta$, and transported Drinfeld data agreeing after composition with powers of $r$. The final series identity provides an explicit witness, with $v$ and the exponent $\varrho.d+j_1+1$, for the isomorphism of rigidified objects used by the statement that corresponding rigidifications give isomorphic transports.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_parity_eq_and_n_eq_and_act_pow_comp_eq_of_isoVia_of_corr_of_isRigTransport_of_isFormalCompletionAlong.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.parity_eq_and_n_eq_and_act_pow_comp_eq_of_isoVia_of_corr_of_isRigTransport_of_isFormalCompletionAlong
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

    (hiinv : i.inv ≫ E.f = E'.f) (v : Series B) (hv : FormalODModule.IsODHom X' X v)
    (hvc : CerednikDrinfeld.QM.IsFormalCompletionAlong θ' θ i.inv hiinv v)
    :
    j' = j ∧ t'.n + ϱ.d + j₁ = t.n + ϱ'.d + i₁ ∧
      η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t' = η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t ∧
      ((X.map (Ideal.Quotient.mk (pIdeal r B))).act ((r : Zp2 r) ^ ((ϱ.d + j₁) + 1))).comp
          ((v.map (Ideal.Quotient.mk (pIdeal r B))).comp t'.ρ) =
        ((X.map (Ideal.Quotient.mk (pIdeal r B))).act ((r : Zp2 r) ^ ((ϱ'.d + i₁) + 1))).comp t.ρ := by sorry
