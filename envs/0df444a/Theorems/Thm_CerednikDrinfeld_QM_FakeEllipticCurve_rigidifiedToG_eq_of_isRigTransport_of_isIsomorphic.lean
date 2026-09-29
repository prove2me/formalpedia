-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_rigidifiedToG_eq_of_isRigTransport_of_isIsomorphic
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.rigidifiedToG_eq_of_isRigTransport_of_isIsomorphic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/3e17f511-2281-51c2-9a7e-ff1c1b8a733c
-- title:
--   The G-point Xi(x) is pinned by any admissible transport
-- statement:
--   The setting is the Čerednik–Drinfeld frame: primes $r \neq \bar r$ and a nonzero level $N$ with $r \nmid N$; a characteristic-zero discrete valuation domain $\mathcal{O}$ with irreducible $\pi$, $\pi$-adically complete, residue ring of cardinality $r$ and $(r) = (\pi)$, with fraction field $K_0$; a characteristic-zero domain $O^{\mathrm{nr}}$ over $\mathcal{O}$ that is $\pi$-adically complete, with $(\pi)$ maximal, every element annihilated mod $\pi$ by a monic polynomial over $\mathcal{O}$, every monic polynomial of positive degree having a root mod $\pi$, and an $\mathcal{O}$-automorphism $\mathrm{Fr}$ with $\mathrm{Fr}(x) \equiv x^r \pmod \pi$; a quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ indefinite and with nonsplit completion exactly at $r$ and $\bar r$, a maximal order $\Lambda$ containing $\mathbb{Z}$ with an order coordinate map `coord` into $\mathbb{Z}_{r^2} \times \mathbb{Z}_{r^2}$ (additive, Frobenius-twisted multiplicative, injective, dense, trace-compatible); a fake elliptic curve $A_0$ over $O^{\mathrm{nr}}/\pi$ with formal $\mathcal{O}_D$-module $X_0$ of height $4$ and formal coordinates $\theta_0$; $\iota : \mathbb{Z}_{r^2} \to O^{\mathrm{nr}}$ and a special formal $\mathcal{O}_D$-module $\Phi$ of height $4$ over $O^{\mathrm{nr}}/(r)$; a moduli package $M$ that is a Zariski sheaf, together with maps $\eta$ sending rigidified modules to points of $M$ and satisfying the three laws that $\eta$ separates admissible rigidified modules exactly up to isomorphism, commutes with base change along admissible objects, and is surjective after a Zariski cover by localisations; an injective map $E_0$ of the centraliser of the $\mathbb{Z}_{r^2}$-action and of $\varpi$ on $\Phi$ into $M_2(K_0)$ whose image coincides with $r^{-m} M_2(\mathcal{O})$ for some $m$; a reduction map $\kappa$ compatible with the quotient maps, and a series $\beta_0$ realising an isogeny of height $4n_0$ from $\Phi$ to $X_0$ pushed along $\kappa$. Given moreover a family $\Xi$ assigning to each rigidified fake elliptic curve over a Noetherian $\mathcal{O}$-algebra with $\pi$ nilpotent a $G$-point of $M$, and the hypothesis that over every connected such algebra $\Xi$ is computed by some rigidity transport: for each rigidified curve $x$ with formal module data $(X,\theta)$ there exist $j \le 1$ and a rigidified module $t$ with $t.X = X$, a transport of the rigidification of $x$ in the coordinates $\theta$ with exponent $j$, admissible over $\psi \circ \mathrm{Fr}^{-j}$, and $\Xi(x) = (\psi \circ \mathrm{Fr}^{-j}, \eta(t))$. The conclusion: if $A$ is a nontrivial connected Noetherian $\mathcal{O}$-algebra in which $\pi$ and $r$ are nilpotent, $\psi : O^{\mathrm{nr}} \to A$ an $\mathcal{O}$-algebra map, $x$ a rigidified fake elliptic curve over $(A,\psi)$ with formal module structure $(X,\theta)$ via `coord`, $j \le 1$, and $t''$ a rigidified module with $t''.X = X$ which is a transport of the rigidification of $x$ in the coordinates $\theta$ with exponent $j$ and is admissible over $\psi \circ \mathrm{Fr}^{-j}$, then for every rigidified module $t$ over $A$ admissible over $\psi \circ \mathrm{Fr}^{-j}$ and isomorphic to $t''$ one has $\Xi_A(x) = (\psi \circ \mathrm{Fr}^{-j}, \eta_A(t))$, as $G$-points of $M$ over $A$.
--
--   This is the rigidity statement for the supersingular dictionary in the Čerednik–Drinfeld comparison: the $G$-point attached to a rigidified fake elliptic curve does not depend on which admissible rigidified special formal module one transports it to, only on its isomorphism class. It is used in the construction of lifts of rigidified curves over Artinian bases, where $\Xi$ must be evaluated on a module produced by a different route than the one appearing in its defining clause.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_rigidifiedToG_eq_of_isRigTransport_of_isIsomorphic.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.rigidifiedToG_eq_of_isRigTransport_of_isIsomorphic
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

    (Ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
        IsNilpotent (algebraMap 𝒪 B π) → FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ → ModuliPackage.GPoint 𝒪 M B)

    (hΞdef :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hBr : IsNilpotent ((r : ℕ) : B))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2),
          x.1.IsFormalModuleVia coord X θ →
          ∃ (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
            FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t ∧
            t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
            Ξ B ψ hB x = ⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hBr, η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t⟩))

    (A : Type) [CommRing A] [IsNoetherianRing A] [Nontrivial A] [Algebra 𝒪 A] (hA : IsNilpotent (algebraMap 𝒪 A π))
    (hconn : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) (hAr : IsNilpotent ((r : ℕ) : A))
    (ψ : Onr →ₐ[𝒪] A) (x : FakeEllipticCurve.RigidifiedCurve r π A₀ A ψ)
    (X : FormalODModule r A) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (hx : x.1.IsFormalModuleVia coord X θ)
    (j : ℕ) (hj : j ≤ 1) (t t'' : Rigidified r Φ A)
    (ht''X : t''.X = X) (ht'' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t'')
    (hadm'' : t''.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] A) : Onr →+* A))
    (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] A) : Onr →+* A))
    (hiso : t''.IsIsomorphic t) :
    Ξ A ψ hA x = ⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hAr, η A ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] A) : Onr →+* A) hAr t⟩ := by sorry
