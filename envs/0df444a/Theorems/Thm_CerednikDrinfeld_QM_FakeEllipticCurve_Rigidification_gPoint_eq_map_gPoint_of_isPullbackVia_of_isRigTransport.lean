-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_gPoint_eq_map_gPoint_of_isPullbackVia_of_isRigTransport
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.gPoint_eq_map_gPoint_of_isPullbackVia_of_isRigTransport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/80a8579b-5dad-57fa-86d0-96f032cab03a
-- title:
--   Base change of the G-point of an admissible transport
-- statement:
--   Fix primes $r \neq \bar r$ and a nonzero level $N$ with $r \nmid N$. Let $\mathcal O$ be a characteristic-zero discrete valuation domain, complete for the adic topology of an irreducible element $\pi$, with residue ring of cardinality $r$ and $(r) = (\pi)$, with fraction field $K_0$; let $Onr$ be a characteristic-zero $\mathcal O$-domain, complete for $(\pi)$, with $(\pi)$ maximal, every element integral over $\mathcal O$ modulo $\pi$, every monic polynomial having a root modulo $\pi$, equipped with an $\mathcal O$-automorphism $Fr$ satisfying $Fr(x) \equiv x^r \pmod \pi$. Let $a, b \in \mathbb Q$ be such that $\mathbb H[\mathbb Q,a,b]$ is indefinite and its completion at a finite place is a division algebra exactly at the places above $r$ and $\bar r$; let $\Lambda$ be a maximal order containing $\mathbb Z$, and $coord : \Lambda \to \mathbb{Z}_{p^2}(r)^2$ an order coordinate. Further data: a fake elliptic curve $A_0$ over $Onr/(\pi)$ with formal module $X_0$ of height $4$ and coordinates $\theta_0$; $\iota : \mathbb{Z}_{p^2}(r) \to Onr$; a special formal $\mathcal O_D$-module $\Phi$ of height $4$ over $Onr/(r)$; a moduli package $M$ over $Onr$ which is a Zariski sheaf, together with $\eta$ assigning points of $M$ to rigidified objects and satisfying the three properties of injectivity modulo isomorphism on admissible objects, compatibility with base change and local surjectivity; an injective $E_0$ from the centraliser of the $\Phi$-endomorphisms into $M_2(K_0)$, commensurable with $M_2(\mathcal O)$ up to $r^m$; a map $\kappa : Onr/(\pi) \to Onr/(r)$ compatible with the quotient maps; and an isogeny $\beta_0$ from $\Phi$ to $X_0 \otimes_\kappa$ of height $4n_0$ (these hypotheses are summarised here). Now let $\varphi : B \to B'$ be a morphism of Noetherian $\mathcal O$-algebras in which $\pi$ and $r$ are nilpotent, $\psi : Onr \to B$ an $\mathcal O$-algebra map, $x = (E,\rho)$ a rigidified curve over $(B,\psi)$ and $x' = (E',\rho')$ one over $(B', \varphi \circ \psi)$, with $g : E' \to E$ exhibiting $E'$ as the pullback of $E$ along $\varphi$ (pullback square, compatibility with group law, $\Lambda$-action and level structure) and $h\rho$ the corresponding compatibility of the two rigidifications. Let $(X,\theta)$ and $(X',\theta')$ be formal-module structures via $coord$ on $E$ and $E'$, and let $j, j' \leq 1$, $t$ a rigidified object over $B$ with $t.X = X$ and $t'$ over $B'$ with $t'.X = X'$, each a rigidification transport of $\rho$, respectively $\rho'$, relative to $(\theta_0, \kappa, \beta_0)$ at parity $j$, respectively $j'$, and each admissible with respect to $\iota$ and the twisted leg $\psi \circ Fr^{-j}$, respectively $(\varphi\circ\psi) \circ Fr^{-j'}$. Then the $G$-point of $M$ over $B'$ with leg $(\varphi\circ\psi)\circ Fr^{-j'}$ and point $\eta_{B'}(t')$ equals the image under $\varphi$ of the $G$-point over $B$ with leg $\psi \circ Fr^{-j}$ and point $\eta_B(t)$; in particular the two legs agree and $\eta_{B'}(t')$ is the base change of $\eta_B(t)$ along $\varphi$.
--
--   This is the functoriality statement for the map from rigidified fake elliptic curves to points of Drinfeld's moduli functor: passing to a pullback curve over a larger base and choosing any admissible transport there gives the base change of the point downstairs, with no choice-dependence. It is the naturality input for the construction of a natural transformation from the rigidified-curve functor to the Drinfeld functor, used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedToG_natural_isRigTransport_of_cover`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedToG_natural_isRigTransport_of_cover).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_gPoint_eq_map_gPoint_of_isPullbackVia_of_isRigTransport.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.gPoint_eq_map_gPoint_of_isPullbackVia_of_isRigTransport
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

    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (hBr : IsNilpotent ((r : ℕ) : B)) (hBr' : IsNilpotent ((r : ℕ) : B'))
    (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B' (φ.comp ψ))
    (g : x'.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') x.1 x'.1 g)
    (hρ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg x.2 x'.2)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (hX : x.1.IsFormalModuleVia coord X θ)
    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t)
    (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    (X' : FormalODModule r B') (θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2) (hX' : x'.1.IsFormalModuleVia coord X' θ')
    (j' : ℕ) (t' : Rigidified r Φ B') (hj' : j' ≤ 1) (ht'X : t'.X = X')
    (htr' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x'.2 θ' j' t')
    (hadm' : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j' : ℤ)) (φ.comp ψ) : Onr →ₐ[𝒪] B') : Onr →+* B'))
    :
    (⟨frobTwist Onr Fr (-(j' : ℤ)) (φ.comp ψ), hBr',
        η B' ((frobTwist Onr Fr (-(j' : ℤ)) (φ.comp ψ) : Onr →ₐ[𝒪] B') : Onr →+* B') hBr' t'⟩ : ModuliPackage.GPoint 𝒪 M B') =
      (⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hBr, η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t⟩ :
        ModuliPackage.GPoint 𝒪 M B).map φ := by sorry
