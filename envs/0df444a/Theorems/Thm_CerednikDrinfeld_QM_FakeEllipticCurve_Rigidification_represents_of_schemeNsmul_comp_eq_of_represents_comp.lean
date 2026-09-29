-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_represents_of_schemeNsmul_comp_eq_of_represents_comp
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.represents_of_schemeNsmul_comp_eq_of_represents_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/44e8bf37-211d-5ac9-971e-008527728a8d
-- title:
--   Divided leg of a rigidification is represented by σ₁
-- statement:
--   Fix a prime $r$, a natural number $N$, rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ containing $1$ and all rational integers, together with a coordinate map $\mathrm{coord}:\Lambda\to \mathbb{Z}_{r^2}\times\mathbb{Z}_{r^2}$ (values in Witt vectors over $\mathbb{F}_{r^2}$) satisfying `IsOrderCoord`: it is additive and injective, sends $1$ to $(1,0)$, is multiplicative for the twisted rule mixing the two legs by $r$ and Frobenius, has dense image modulo every power of $r$, and matches reduced traces. Let $\mathcal{O}$ be a commutative ring, $\pi\in\mathcal{O}$, $Onr$ an $\mathcal{O}$-algebra, $k_0=Onr/(\pi)$; let $A_0$ be a fake elliptic curve over $k_0$ with level structure data for $\Lambda,N$, $X_0$ a formal $\mathcal{O}_D$-module of dimension $2$ over $k_0$ and $\theta_0$ formal coordinates of $A_0.f$ in $2$ variables, with $A_0$ a formal module via $\mathrm{coord},X_0,\theta_0$. Let $B$ be a Noetherian $\mathcal{O}$-algebra, $\psi:Onr\to B$ an $\mathcal{O}$-algebra map, $\bar B=B/(\pi)$, with $r$ nilpotent in $\bar B$, and let $E/B$ be a fake elliptic curve that is a formal module via $\mathrm{coord}$, a formal $\mathcal{O}_D$-module $X$ over $B$ and coordinates $\theta$. Let $\rho$ be a rigidification of $E$ relative to $A_0$ and $\psi$, so $\rho$ supplies fake elliptic curves $\rho.Eb,\rho.Ab$ over $\bar B$ with pullback maps $\rho.gb:\rho.Eb.A\to E.A$ and $\rho.gA:\rho.Ab.A\to A_0.A$ (the latter along the induced map $k_0\to\bar B$, written `residueLeg`), an exponent $d$ and an isogeny pair $\rho.\varphi,\rho.\varphi'$ of degree $r^d$ between $\rho.Eb$ and $\rho.Ab$. Assume a pair of power series $\sigma$ over $\bar B$ represents $\rho.\varphi'$ followed by $\rho.gb$ on nilpotent points: for every ring $B''$ that is simultaneously an algebra over $\bar B$, over $B$ and over $k_0$, compatibly in the sense that $B\to B''$ factors through $\bar B$ and $k_0\to B''$ factors through `residueLeg`, every ideal $J$ with $J^{m+1}=0$, every $s:\mathrm{Fin}\,2\to J$ and every $B''$-point $P_A$ of $\rho.Ab.A$ over $\mathrm{Spec}\,\bar B$ with $P_A$ followed by $\rho.gA$ equal to $\theta_0(s)$, the composite of $P_A$ with $\rho.\varphi'$ and then $\rho.gb$ equals $\theta(\mathrm{nilEval}_m(\sigma_i)(s))$. Assume further a natural number $k$ and a pair $\gamma$ of series over $k_0$ with zero constant terms representing the action of $r^k\in\Lambda$ on $A_0$ in the coordinates $\theta_0$, a pair $\sigma_1$ over $\bar B$ with zero constant terms and the factorisation $\sigma=\sigma_1\circ(\text{image of }\gamma\text{ under }\mathrm{residueLeg})$, and finally a morphism $\psi':\rho.Ab.A\to\rho.Eb.A$ over $\bar B$ which is $\Lambda$-equivariant, is a homomorphism for the relative group laws on $T$-points, and satisfies $\mathrm{schemeNsmul}(r^k)$ for $\rho.Ab.L$ followed by $\psi'$ equals $\rho.\varphi'$. The conclusion is that $\sigma_1$ represents $\psi'$ followed by $\rho.gb$ in exactly the same sense: under the same hypotheses on $B'',J,m,s$ and $P_A$, the composite of $P_A$ with $\psi'$ and then $\rho.gb$ equals $\theta(\mathrm{nilEval}_m((\sigma_1)_i)(s))$.
--
--   This is the cancellation step for the germ of the divided leg of a rigidification: once the leg $\rho.\varphi'$ factors as multiplication by $r^k$ followed by $\psi'$, and its representing pair of series factors correspondingly as $\sigma_1$ composed with the series for $[r^k]$, the quotient series $\sigma_1$ is shown to represent $\psi'$ on all nilpotent points. It is used in the assembly of equivalences of admissible rigidifications over Artinian and over local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_represents_of_schemeNsmul_comp_eq_of_represents_comp.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.represents_of_schemeNsmul_comp_eq_of_represents_comp
    {r N : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (hBr : IsNilpotent ((r : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hX : E.IsFormalModuleVia coord X θ)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)

    (σ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (hσ : ∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1)

    (k : ℕ) (γ : Series (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0)
    (hγ : ∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (n : ℕ),
        J ^ (n + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval n (γ i) s) =
            pushPt (A₀.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (A₀.act_over _) (θ₀ B' s))
    (σ₁ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (hσ₁ : ∀ i, MvPowerSeries.constantCoeff (σ₁ i) = 0)
    (hdiv : σ = σ₁.comp (γ.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)))

    (ψ' : ρ.Ab.A ⟶ ρ.Eb.A) (hfac : ρ.Ab.L.schemeNsmul (r ^ k) ≫ ψ' = ρ.φ')
    (hψ'lin : ∀ x : ↥Λ, ρ.Ab.act x ≫ ψ' = ψ' ≫ ρ.Eb.act x)
    (hψ'f : ψ' ≫ ρ.Eb.f = ρ.Ab.f)
    (hψ'hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P Q : SchemeHomOver t ρ.Ab.f),
      (ρ.Ab.L.mul t P Q).1 ≫ ψ' =
        (ρ.Eb.L.mul t ⟨P.1 ≫ ψ', by rw [Category.assoc, hψ'f]; exact P.2⟩
          ⟨Q.1 ≫ ψ', by rw [Category.assoc, hψ'f]; exact Q.2⟩).1) :
    ∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ψ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ₁ i) s)).1 := by sorry
