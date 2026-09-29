-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_one_of_isRigTransport_add_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_one_of_isRigTransport_add_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/0225b8b1-e888-59fc-a57f-fd386cf3522e
-- title:
--   Transports of parities j and j+2 differ by Frobenius square
-- statement:
--   Fix primes $r,\bar r$ with $\bar r\neq r$ and $N\neq 0$ with $r\nmid N$. Let $\mathcal O$ be a characteristic-zero domain that is a discrete valuation ring, $\pi$ an irreducible element, $\mathcal O$ complete for the $(\pi)$-adic topology, with $\#(\mathcal O/\pi)=r$ and $(r)=(\pi)$, and $K_0$ a characteristic-zero fraction field of $\mathcal O$; let $\mathrm{Onr}$ be a characteristic-zero $\mathcal O$-domain with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, complete for $(\pi)$, with $(\pi)$ maximal, every element a root mod $\pi$ of a monic polynomial over $\mathcal O$, every monic polynomial of positive degree having a root mod $\pi$, and $\mathrm{Fr}(x)\equiv x^{r}\pmod\pi$. Let $a,b\in\mathbb Q$ with $\mathbb H[\mathbb Q,a,b]$ indefinite and ramified exactly at the places above $r$ and $\bar r$, $\Lambda$ a maximal order containing $\mathbb Z$, and $\mathrm{coord}:\Lambda\to\mathbb Z_{r^2}\times\mathbb Z_{r^2}$ an order coordinate (additive, $1\mapsto(1,0)$, multiplicative for the $\varpi$-twisted rule, injective, dense, trace-compatible). Further data: a fake elliptic curve $A_0$ over $\mathrm{Onr}/\pi$ with formal coordinates $\theta_0$ presenting it via $\mathrm{coord}$ as a formal $\mathcal O_D$-module $X_0$ of height $4$; a ring map $\iota:\mathbb Z_{r^2}\to\mathrm{Onr}$; a special formal $\mathcal O_D$-module $\Phi$ of height $4$ over $\mathrm{Onr}/r$; a moduli package $M$ satisfying the Zariski sheaf axioms, together with $\eta$ sending rigidified objects to points of $M$ and the hypotheses that $\eta$ separates admissible objects exactly up to isomorphism, is natural in ring maps, and is locally surjective; an injective ring map $E_0$ from the centralizer of the $\mathbb Z_{r^2}$-action and $\varpi$ on $\Phi$ into $M_2(K_0)$ whose image is commensurable with $M_2(\mathcal O)$ (an exponent $m$ with $r^{m}M_2(\mathcal O)$ inside the image and $r^{m}$ times the image inside $M_2(\mathcal O)$); a ring map $\kappa:\mathrm{Onr}/\pi\to\mathrm{Onr}/r$ compatible with the quotient maps; and a series $\beta_0$ realising an isogeny $\Phi\to X_0\otimes_\kappa$ of height $4n_0$. Let $B$ be an $\mathcal O$-algebra with $\pi$ nilpotent, $\psi:\mathrm{Onr}\to_{\mathcal O} B$, and $x=(E,\varrho)$ a rigidified curve over $(B,\psi)$ with formal coordinates $(X,\theta)$ for $E$ via $\mathrm{coord}$. Suppose $t$ and $t_2$ are rigidified objects with $t.X=t_2.X=X$, with $\rho$-series of zero constant term, which are rig transports of $\varrho$ relative to $(\theta_0,\kappa,\beta_0,\theta)$ of parities $j$ and $j+2$ respectively, and $t_2.n=t.n+1$. Then `Rigidified.IsTranslate` holds for the identity series, $k=1$, $m'=0$ and the leg $\psi\circ\mathrm{Fr}^{-j}$: that is, $t_2.X=t.X$ and there is $c\in\mathbb N$ with $[r^{\,c+t.n+1}]\circ t_2.\rho=[r^{\,c+t_2.n}]\circ t.\rho\circ(X_i\mapsto X_i^{r^2})$, the multiplications being by the action of $r$ on the reduction of $X$.
--
--   This is the parity bookkeeping of the supersingular dictionary in the Čerednik–Drinfeld uniformisation: two transports of one rigidification whose Frobenius parities differ by $2$ differ by the square of the Frobenius substitution, with the level index shifted by one. It is used in the construction of the scalar action on $G$-points attached to a rigidified curve via the inverse Frobenius twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_one_of_isRigTransport_add_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_one_of_isRigTransport_add_two
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

    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (hX : x.1.IsFormalModuleVia coord X θ)
    (j : ℕ) (t : Rigidified r Φ B) (htX : t.X = X) (ht0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t)
    (t₂ : Rigidified r Φ B) (ht₂X : t₂.X = X) (ht₂0 : ∀ i, MvPowerSeries.constantCoeff (t₂.ρ i) = 0)
    (htr₂ : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ (j + 2) t₂)
    (hn : t₂.n = t.n + 1) :
    Rigidified.IsTranslate (Series.id (Onr ⧸ pIdeal r Onr)) 1 0 ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) t t₂ := by sorry
