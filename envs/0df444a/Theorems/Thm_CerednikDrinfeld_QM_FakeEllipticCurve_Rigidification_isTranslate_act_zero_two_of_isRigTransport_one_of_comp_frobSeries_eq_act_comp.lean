-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_act_zero_two_of_isRigTransport_one_of_comp_frobSeries_eq_act_comp
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_act_zero_two_of_isRigTransport_one_of_comp_frobSeries_eq_act_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/3bba14cd-fe5f-522b-ae6e-f6d8ac235e72
-- title:
--   Parity-one transport as a ([r],0,2)-translate
-- statement:
--   Fix primes $r$ and $\bar r$ with $\bar r \neq r$ and a nonzero $N$ with $r \nmid N$, and work in the following arithmetic frame: $\mathcal{O}$ is a characteristic-zero discrete valuation domain with irreducible element $\pi$, $\pi$-adically complete, with $\#(\mathcal{O}/\pi) = r$ and $(r) = (\pi)$, with fraction field $K_0$; $Onr$ is a characteristic-zero domain over $\mathcal{O}$, complete for $(\pi)$, with $(\pi)$ maximal, each element integral over $\mathcal{O}$ modulo $\pi$, each monic polynomial of positive degree having a root modulo $\pi$, and equipped with an $\mathcal{O}$-algebra automorphism $F_r$ with $F_r(x) \equiv x^r \pmod{\pi}$. Further, $a,b \in \mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt a b r rbar` (that is, $a > 0$ or $b > 0$, and a finite place of $\mathbb{Q}$ is nonsplit for $\mathbb{H}[\mathbb{Q},a,b]$ exactly when it lies over $r$ or over $\bar r$); $\Lambda$ is a maximal order of $\mathbb{H}[\mathbb{Q},a,b]$ containing the integers, and `coord` is an order coordinate $\Lambda \to \mathrm{Zp2}\,r \times \mathrm{Zp2}\,r$ in the sense of `IsOrderCoord` (additive, unital, multiplicative for the twisted rule, injective, dense, and computing traces), where $\mathrm{Zp2}\,r = \mathrm{WittVector}\,r(\mathbb{F}_{r^2})$. Over the residue ring $Onr/\pi$ one is given a fake elliptic curve $A_0$ of level $N$ for $\Lambda$, a formal $\mathcal{O}_D$-module $X_0$ of height $4$, relative formal coordinates $\theta_0$ of dimension $2$ on $A_0$, and the compatibility `IsFormalModuleVia` between them; a ring map $\iota : \mathrm{Zp2}\,r \to Onr$; a formal $\mathcal{O}_D$-module $\Phi$ over $Onr/(r)$ which is special for $\iota$ reduced and of height $4$; a moduli package $M$ over $Onr$ satisfying the Zariski sheaf condition, together with a family $\eta$ attaching to every rigidified object over a ring in which $r$ is nilpotent a point of $M$, subject to the three conditions that on admissible objects $\eta$ separates exactly the isomorphism classes, that $\eta$ is compatible with base change, and that every point of $M$ comes locally on a finite cover of the base by localisations from an admissible rigidified object; an injective ring map $E_0$ from the centraliser of the $\mathrm{Zp2}\,r$-action and of $\varpi$ on $\Phi$ into $M_2(K_0)$ whose image agrees with $M_2(\mathcal{O})$ up to a fixed power of $r$; the reduction map $\kappa : Onr/\pi \to Onr/(r)$ compatible with the quotient maps; and an isogeny $\beta_0$ of height $4n_0$ from $\Phi$ to $X_0$ pushed forward along $\kappa$. Now let $B$ be an $\mathcal{O}$-algebra in which $\pi$ is nilpotent, $\psi : Onr \to B$ an $\mathcal{O}$-algebra map, and $x$ a rigidified curve over $(B,\psi)$, that is, a fake elliptic curve together with a rigidification relative to $A_0$; let $X$ be a formal $\mathcal{O}_D$-module over $B$ and $\theta$ formal coordinates making the curve underlying $x$ a formal module via `coord`, $X$ and $\theta$. Let $t$ be a rigidified object over $B$ with $t.X = X$, all constant terms of $t.\rho$ zero, which is a rigidification transport of $x$ of parity $1$ with respect to $\theta_0$, $\kappa$, $\beta_0$ and $\theta$, and suppose $t$ is admissible for $\iota$ and a ring map $\chi : Onr \to B$; let $t''$ satisfy the same conditions with parity $0$ in place of $1$; and let $t'$ have $t'.X = X$, zero constant terms, $t'.n = t.n$, and satisfy $t'.\rho \circ \mathrm{Frob} = [r]_{\overline{t''.X}} \circ t''.\rho$, where $\mathrm{Frob}$ denotes the substitution $X_i \mapsto X_i^{r}$ over $B/(r)$. Then $t'$ is a translate of $t$ with data $([r]_\Phi, 0, 2)$ along $\chi$: $t'.X = t.X$ and there is $c$ with $[r^{c+t.n}]_{\overline{t.X}} \circ (t'.\rho \circ \mathrm{Frob}^{2}) = [r^{c+t'.n}]_{\overline{t.X}} \circ (t.\rho \circ \overline{\chi}([r]_\Phi))$, the last substitution being by the identity series.
--
--   This is a step in the supersingular dictionary of the Čerednik–Drinfeld uniformisation, where transports of a rigidification of different parities are compared: passing from parity $1$ to the re-based data exhibits the re-based object as a Frobenius translate with shift $m' = 2$ and $k = 0$. It feeds the construction of the point of the moduli package on which Frobenius acts by a scalar power, used in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isActBy_scalar_zpow_rigidifiedToG_frobTwist_one_of_comp_relFrobenius`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isActBy_scalar_zpow_rigidifiedToG_frobTwist_one_of_comp_relFrobenius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_act_zero_two_of_isRigTransport_one_of_comp_frobSeries_eq_act_comp.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_act_zero_two_of_isRigTransport_one_of_comp_frobSeries_eq_act_comp
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
    (t : Rigidified r Φ B) (htX : t.X = X) (ht0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ 1 t)
    (χ : Onr →+* B) (hadm : t.IsAdmissible ι χ)
    (t'' : Rigidified r Φ B) (ht''X : t''.X = X) (ht''0 : ∀ i, MvPowerSeries.constantCoeff (t''.ρ i) = 0)
    (htr'' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ 0 t'')
    (t' : Rigidified r Φ B) (ht'X : t'.X = X) (ht'0 : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0) (hn : t'.n = t.n)
    (hrel : t'.ρ.comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) 1) = (t''.Xbar.act (r : Zp2 r)).comp t''.ρ) :
    Rigidified.IsTranslate (Φ.act (r : Zp2 r)) 0 2 χ t t' := by sorry
