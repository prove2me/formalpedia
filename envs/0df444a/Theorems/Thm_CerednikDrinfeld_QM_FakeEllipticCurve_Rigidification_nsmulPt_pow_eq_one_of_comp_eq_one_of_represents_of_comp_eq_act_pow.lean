-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nsmulPt_pow_eq_one_of_comp_eq_one_of_represents_of_comp_eq_act_pow
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.nsmulPt_pow_eq_one_of_comp_eq_one_of_represents_of_comp_eq_act_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/122e2dbb-81fd-5cc1-855d-9b20f8ec4c15
-- title:
--   Kernel of the divided leg is killed by r^h
-- statement:
--   Fix a prime $r$, a natural number $N$, rationals $a,b$, and a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ containing $1$ and all integer scalars, together with a map $\mathrm{coord} : \Lambda \to \mathbb{Z}_{r^2}^{\,2}$ that is additive, sends $1$ to $(1,0)$, is multiplicative for the twisted rule of `IsOrderCoord`, is injective, has dense image modulo every power of $r$, and matches reduced traces. Let $\mathcal{O}$ be a commutative ring, $\pi \in \mathcal{O}$, $O^{nr}$ an $\mathcal{O}$-algebra, $A_0$ a fake elliptic curve over $O^{nr}/\pi$ with level structure $N$ and $\Lambda$-action, $X_0$ a formal $\mathcal{O}_D$-module over $O^{nr}/\pi$ of dimension $2$ with $\mathbb{Z}_{r^2}$-action and uniformiser series, and $\theta_0$ formal coordinates for $A_0.f$ in two variables exhibiting $A_0$ as formal module via $\mathrm{coord}$ and $X_0$. Let $B$ be a Noetherian $\mathcal{O}$-algebra in which $r$ is nilpotent modulo $\pi$, $\psi : O^{nr} \to B$ an $\mathcal{O}$-algebra map, $E$ a fake elliptic curve over $B$ with formal module data $(X,\theta)$, and $\rho$ a rigidification of $E$ relative to $r$, $\pi$, $A_0$ and $\psi$, with reductions $E_b$, $A_b$ over $B/\pi$, comparison maps $g_b$, $g_A$, isogeny legs $\varphi$, $\varphi'$ and exponent $d$. Suppose given $k \in \mathbb{N}$ and $\psi' : A_b \to E_b$ such that multiplication by $r^k$ on $A_b$ followed by $\psi'$ equals $\varphi'$, that $\psi'$ is a morphism over $B/\pi$ (i.e. $\psi'$ followed by $E_b.f$ is $A_b.f$), and that $\psi'$ is a homomorphism for the relative group laws on all points over all bases. Suppose further that a pair of power series $\sigma_1$ over $B/\pi$ with vanishing constant terms represents $\psi'$ followed by $g_b$ in the coordinates: for every $B/\pi$-algebra $B''$ that is also a $B$-algebra and an $O^{nr}/\pi$-algebra, with structure maps compatible via the quotient map $B \to B/\pi$ and via `residueLeg` of $\pi$ and $\psi$, for every ideal $J$ with $J^{m+1} = 0$, every $s : \mathrm{Fin}\,2 \to J$ and every point $P_A$ of $A_b$ over $\operatorname{Spec} B''$ with $P_A$ followed by $g_A$ equal to $\theta_0(s)$, the point $P_A$ followed by $\psi'$ and $g_b$ equals $\theta$ evaluated at the truncated values of $\sigma_1$ at $s$. Finally let $h \in \mathbb{N}$ and let $\delta$ be a pair of power series over $B/\pi$ with vanishing constant terms such that $\delta \circ \sigma_1$ equals the action of $r^h \in \mathbb{Z}_{r^2}$ on the base change of $X_0$ along `residueLeg`. Then for every scheme $T$, every $t : T \to \operatorname{Spec}(B/\pi)$ and every point $P$ of $A_b$ over $t$, if $P$ followed by $\psi'$ is the identity section of $E_b$ over $t$, then $r^h \cdot P$ is the identity section of $A_b$ over $t$.
--
--   This is the scheme-theoretic kernel bound for the divided leg of a rigidification: a formal left quasi-inverse $\delta$ of the series $\sigma_1$ representing $\psi'$ forces the kernel of $\psi'$ to be annihilated by $r^h$, with no assumption relating $h$ to the exponent $k$ in the factorisation of $\varphi'$. It discharges the kernel hypothesis in the construction of isogeny pairs of rigidifications, and is used in the two comparison results `exists_le_equiv_of_isAdmissible_of_n_le_of_isArtinianRing` and `exists_le_equiv_of_isAdmissible_of_n_le_of_isLocalRing`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nsmulPt_pow_eq_one_of_comp_eq_one_of_represents_of_comp_eq_act_pow.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.nsmulPt_pow_eq_one_of_comp_eq_one_of_represents_of_comp_eq_act_pow
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

    (k : ℕ) (ψ' : ρ.Ab.A ⟶ ρ.Eb.A) (hfac : ρ.Ab.L.schemeNsmul (r ^ k) ≫ ψ' = ρ.φ')
    (hψ'f : ψ' ≫ ρ.Eb.f = ρ.Ab.f)
    (hψ'hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P Q : SchemeHomOver t ρ.Ab.f),
      (ρ.Ab.L.mul t P Q).1 ≫ ψ' =
        (ρ.Eb.L.mul t ⟨P.1 ≫ ψ', by rw [Category.assoc, hψ'f]; exact P.2⟩
          ⟨Q.1 ≫ ψ', by rw [Category.assoc, hψ'f]; exact Q.2⟩).1)

    (σ₁ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (hσ₁ : ∀ i, MvPowerSeries.constantCoeff (σ₁ i) = 0)
    (hσ₁rep : ∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ψ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ₁ i) s)).1)

    (h : ℕ) (δ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (hδ0 : ∀ i, MvPowerSeries.constantCoeff (δ i) = 0)
    (hδσ : δ.comp σ₁ = (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ h)) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P : SchemeHomOver t ρ.Ab.f),
      P.1 ≫ ψ' = (ρ.Eb.L.one t).1 → nsmulPt ρ.Ab.L t (r ^ h) P = ρ.Ab.L.one t := by sorry
