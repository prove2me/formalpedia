-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isRigTransport_isAdmissible_of_isFormalModuleVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isRigTransport_isAdmissible_of_isFormalModuleVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/08a6e8b6-6599-5595-a15e-3a300b88a3c4
-- title:
--   Transport of a rigidification to an admissible rigidified module
-- statement:
--   Fix primes $r$ and $\bar r$ with $\bar r \neq r$ and a nonzero $N$ not divisible by $r$. Let $\mathcal O$ be a characteristic-zero discrete valuation domain with irreducible element $\pi$, complete for the $\pi$-adic topology, with $\#(\mathcal O/\pi)=r$ and $(r)=(\pi)$, and let $K_0$ be a characteristic-zero fraction field of $\mathcal O$; let $O^{\mathrm{nr}}$ be a characteristic-zero $\mathcal O$-domain, complete for the $\pi$-adic topology, with $(\pi)$ maximal, every element integral over $\mathcal O$ modulo $\pi$ and every monic polynomial of positive degree having a root modulo $\pi$, carrying an $\mathcal O$-algebra automorphism $\mathrm{Fr}$ with $\mathrm{Fr}(x)\equiv x^{r}$ modulo $\pi$. Let $\mathbb H[\mathbb Q,a,b]$ be indefinite and ramified exactly at $r$ and $\bar r$, $\Lambda$ a maximal order containing $\mathbb Z$, and $\mathrm{coord}:\Lambda \to \mathbb Z_{r^2}\times\mathbb Z_{r^2}$ an order coordinatisation at $r$ (additive, unital, twisted multiplicative, injective, dense, trace-compatible). Over $O^{\mathrm{nr}}/\pi$ are given a fake elliptic curve $A_0$ with level $N$, a formal $\mathcal O_D$-module $X_0$ of height $4$ and two-dimensional formal coordinates $\theta_0$ for $A_0$ with $A_0.\mathrm{IsFormalModuleVia}\ \mathrm{coord}\ X_0\ \theta_0$. Further data: $\iota : \mathbb Z_{r^2}\to O^{\mathrm{nr}}$; a special formal $\mathcal O_D$-module $\Phi$ of height $4$ over $O^{\mathrm{nr}}/r$ for the structure map induced by $\iota$; a moduli package $M$ over $O^{\mathrm{nr}}$ which is a Zariski sheaf, together with maps $\eta$ from rigidified objects to $M$-points satisfying, on Noetherian bases, injectivity up to isomorphism on admissible objects, naturality in the base, and local representability of every $M$-point by an admissible rigidified object after a Zariski cover; an injective ring map $E_0$ from the centraliser of the $\mathbb Z_{r^2}$-action and of $\varpi$ on $\Phi$ into $M_2(K_0)$ whose image is commensurable with $M_2(\mathcal O)$ in the sense that for some $m$ one has $r^m M_2(\mathcal O) \subseteq \mathrm{im}\,E_0$ and $r^m\,\mathrm{im}\,E_0 \subseteq M_2(\mathcal O)$; a ring map $\kappa : O^{\mathrm{nr}}/\pi \to O^{\mathrm{nr}}/r$ compatible with the quotient maps; and $\beta_0$, a pair of power series which is an isogeny of height $4n_0$ from $\Phi$ to the base change of $X_0$ along $\kappa$. Finally let $B$ be a Noetherian $\mathcal O$-algebra in which $\pi$ and $r$ are nilpotent and whose only idempotents are $0$ and $1$, let $\psi : O^{\mathrm{nr}} \to B$ be an $\mathcal O$-algebra map, $E$ a fake elliptic curve over $B$ with level $N$, $\rho$ a rigidification of $E$ relative to $(r,\pi,A_0,\psi)$, and $(X,\theta)$ a formal $\mathcal O_D$-module with coordinates satisfying $E.\mathrm{IsFormalModuleVia}\ \mathrm{coord}\ X\ \theta$. The conclusion: there are a natural number $j \le 1$ and a rigidified object $t$ over $B$ for $\Phi$ with $t.X = X$, with $\mathrm{IsRigTransport}\ \theta_0\ \kappa\ \beta_0\ \rho\ \theta\ j\ t$ — that is, there are a ring map $\kappa_B : B/\pi \to B/r$ compatible with the quotient maps and with $\kappa$ along the two residue legs, and a pair $\sigma$ of power series over $B/\pi$ representing on nilpotent points the morphism $\rho.\varphi'$ followed by $\rho.g_b$, read through $\theta_0$ pulled back along $\rho.g_A$ and through $\theta$, such that $t.\rho$ is the composite of $\sigma$ pushed to $B/r$, of $\beta_0$ pushed along the residue map of $\psi$, and of the $r^{j}$-power substitution — and with $t$ admissible for $\iota$ and the Frobenius-twisted leg $\psi \circ \mathrm{Fr}^{-j}$: $t.X$ is special for the resulting structure map, has height $4$, and $t.\rho$ is an isogeny of height $4\,t.n$ from $\Phi$ base-changed to $B/r$ to $X$ modulo $r$.
--
--   This is the existence half of the defining clause of the Čerednik–Drinfeld dictionary between fake elliptic curves with a rigidification and rigidified special formal $\mathcal O_D$-modules: over a connected coordinatised base it produces, from the geometric side, the rigidified object together with the Frobenius twist $\mathrm{Fr}^{-j}$, $j \le 1$, of the coefficient leg for which it is admissible. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedToG_natural_isRigTransport_of_cover`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedToG_natural_isRigTransport_of_cover), which glues such witnesses over a cover by connected coordinatised pieces into a natural transformation to the moduli functor of $M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isRigTransport_isAdmissible_of_isFormalModuleVia.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isRigTransport_isAdmissible_of_isFormalModuleVia
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
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ) :
    ∃ (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
      FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j t ∧
      t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) := by sorry
