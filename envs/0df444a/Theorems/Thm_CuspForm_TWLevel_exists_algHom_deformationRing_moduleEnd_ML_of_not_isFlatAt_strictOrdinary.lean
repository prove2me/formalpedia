-- Prove2me | Theorems.Thm_CuspForm_TWLevel_exists_algHom_deformationRing_moduleEnd_ML_of_not_isFlatAt_strictOrdinary
-- name    : CuspForm.TWLevel.exists_algHom_deformationRing_moduleEnd_ML_of_not_isFlatAt_strictOrdinary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/0edf0082-c11c-52a7-bcf1-e038230480ee
-- title:
--   R_Q acting on the Taylor–Wiles module, très ramifié case
-- statement:
--   Fix a characteristic-zero complete discrete valuation ring $\mathcal O$ with finite residue field $k$, and an odd prime $p$ with $p \in \mathfrak m_{\mathcal O}$. Let $\bar\rho$ be a two-dimensional residual representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over $k$ whose base change to $\overline k$ is irreducible, and let $p \in S_{\min} \subseteq S$ be finite sets of primes such that a prime $q \neq p$ lies in $S_{\min}$ exactly when $\bar\rho$ is ramified at $q$, with $\bar\rho$ having characteristic polynomial $(X-1)^2$ on inertia at each $q \in S_{\min}$, $q \neq p$. Let $N$ be squarefree, with all prime divisors in $S$, divisible by every $q \in S_{\min} \setminus \{p\}$, with every prime divisor $\neq p$ in $S_{\min}$, and with $p \mid N$, and assume $\bar\rho$ fails the finite-flat condition `GaloisRep.IsFlatAt` at $p$. An auxiliary prime $r \geq 5$ is chosen with $r \notin S$, $r \nmid Np$, $p \nmid r-1$ and $\operatorname{tr}\bar\rho(\sigma)^2 \neq (r+1)^2$ for every Frobenius $\sigma$ at every place over $r$; weight-two cusp forms of level $N$ are assumed to have an integral structure. Further data: a ring homomorphism $\theta$ from the Hecke algebra $\mathbb T^S(N)$ of weight $2$ to $k$ matching the characteristic polynomials $X^2 - \theta(T_\ell)X + \ell$ of Frobenius in $\bar\rho$ for primes $\ell \nmid N$, $\ell \notin S$; finitely many distinct Taylor–Wiles primes $q_i \geq 5$ outside $S$ with $p \mid q_i - 1$, together with roots $\alpha_i \in k$ of $X^2 - \theta(T_{q_i})X + q_i$ satisfying $2\alpha_i \neq \theta(T_{q_i})$; universal deformation data $D_{\min}$ for the minimal strict-ordinary type at $(p, S_{\min})$ and $D_Q$ for the type that is strict ordinary for $S_{\min} \cup \{q_i\}$ and unipotent on inertia at the primes of $S_{\min}$ other than $p$; a local $\mathcal O$-algebra map $\varphi_0$ from $D_{\min}.R$ to the local Hecke ring $\mathbb T =$ `heckeLocal` $N\,S\,\mathcal O\,\theta$ for which the base change of $D_{\min}.\rho$ has Frobenius characteristic polynomials $X^2 - \pi(T_\ell)X + \ell$; cyclotomic characters $\mathrm{cyc}$ and surjections $\pi_\Delta$ onto the groups $\mathrm{Multiplicative}(\mathbb Z/p^{v_p(q_i-1)})$; an $\mathcal O$-algebra map $\varepsilon : D_Q.R \to D_{\min}.R$, local and with $D_Q.\rho$ base changing to a representation equivalent to $D_{\min}.\rho$, and an $\mathcal O$-algebra map $\iota$ from the group algebra $\mathcal O[\Delta]$, $\Delta = \prod_i \mathrm{Multiplicative}(\mathbb Z/p^{v_p(q_i-1)})$, into $D_Q.R$ killed by $\varepsilon$ on group elements and diagonalising $D_Q.\rho$ on inertia at each $q_i$ with characters $\iota(\pi_\Delta(\mathrm{cyc}))^{\pm 1}$ in the $i$-th coordinate. Finally, commutation hypotheses `hcQ` and `hdc` for the Hecke and diamond operators on the cohomology carrier of level $N(\prod_i q_i)r$ and subgroup $H_Q$, and an $\mathcal O$-module $L$, finite over $\mathcal O$ and a module over $\mathbb T$ compatibly, together with an $\mathcal O$-linear map $\lambda$ from $M_Q :=$ `ML` (the localisation of that carrier at the complement of the prime $\ker\tilde\theta$ cut out by $\theta$ and the $\alpha_i$) to $L$ carrying the free-algebra generator $T_\ell$ to the image of $T_\ell$ in $\mathbb T$ and invariant under the diamond operators $\mathrm{dia}_u$ for $u \in H_R$. Under these hypotheses there exist a group automorphism $\kappa$ of $\Delta$ and an $\mathcal O$-algebra homomorphism $\psi : D_Q.R \to \mathrm{End}_{\mathcal O}(M_Q)$ such that $\psi(\iota(\kappa(\pi_Q(u)))) = \mathrm{dia}_u$ for all $u \in H_R$, and $\lambda(\psi(x)m) = \varphi_0(\varepsilon(x))\cdot\lambda(m)$ for all $x \in D_Q.R$ and $m \in M_Q$.
--
--   This is the Galois side of the Taylor–Wiles construction in the case $p \mid N$ with $\bar\rho$ not finite flat at $p$ (the très ramifié, strict ordinary type): the universal deformation ring $R_Q$ of the relaxed type acts on the localised cohomology module $M_Q$ of level $\Gamma_0(N) \cap \Gamma_1(r) \cap \Gamma_{H_Q}$, the diamond operators of $H_R$ being realised through the group-algebra part $\mathcal O[\Delta]$ up to an automorphism of $\Delta$, and the action being compatible via $\lambda$ with the minimal-level action through $\varepsilon$ and $\varphi_0$. It is used by [`CuspForm.heckeLocal.exists_taylorWilesModule_of_linearEquiv_ML_of_not_isFlatAt_strictOrdinary`](thm.html#CuspForm.heckeLocal.exists_taylorWilesModule_of_linearEquiv_ML_of_not_isFlatAt_strictOrdinary), which packages $M_Q$ as a Taylor–Wiles module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_TWLevel_exists_algHom_deformationRing_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.lean

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_TWLevelHeckeModule
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Polynomial IsLocalRing CuspForm.TWLevel

theorem CuspForm.TWLevel.exists_algHom_deformationRing_moduleEnd_ML_of_not_isFlatAt_strictOrdinary
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S Smin : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)

    (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (hNmin : ∀ q ∈ Smin, q ≠ p → q ∣ N)
    (hN : Squarefree N ∧ ∀ q : ℕ, q.Prime → q ≠ p → q ∣ N → q ∈ Smin)

    (hpN : p ∣ N) (hnfl : ¬ (GaloisRepAdic.ofResidualGaloisRep ρbar).IsFlatAt p)

    (r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r) (hrS : r ∉ S) (hrN : ¬ r ∣ N * p) (hr1 : ¬ p ∣ r - 1)
    (hrρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
        LinearMap.trace (ResidueField 𝒪) ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : ResidueField 𝒪) + 1) ^ 2)
    [Fact (CuspForm.HasIntegralStructure N 2)]

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (t : ℕ) (qv : Fin t → ℕ) (hqinj : Function.Injective qv)
    (hqv : ∀ i, (qv i).Prime ∧ qv i ∉ S ∧ p ∣ qv i - 1) (hq5 : ∀ i, 5 ≤ qv i)
    (α : Fin t → ResidueField 𝒪)
    (hα : ∀ i, α i ^ 2 - θ (CuspForm.heckeAlgebra.T (hqv i).1
        (fun h => (hqv i).2.1 (hNS _ (hqv i).1 h)) (hqv i).2.1) * α i + (qv i : ResidueField 𝒪) = 0 ∧
      2 * α i ≠ θ (CuspForm.heckeAlgebra.T (hqv i).1 (fun h => (hqv i).2.1 (hNS _ (hqv i).1 h)) (hqv i).2.1))

    (Dmin : GaloisRep.DeformationRingData 𝒪 ρbar (GaloisRep.minimalStrictOrdinaryCondition 𝒪 p Smin))
    (DQ : GaloisRep.DeformationRingData 𝒪 ρbar (fun _A _ _ _ ρ =>
      GaloisRep.strictOrdinaryCondition 𝒪 p (Smin ∪ Finset.univ.image qv) ρ ∧
        ∀ q ∈ Smin, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q))

    (φ₀ : Dmin.R →ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ)
    (hφ₀ : IsLocalHom (φ₀ : Dmin.R →+* CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ))
    (hES₀ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly ((Dmin.ρ.baseChangeAlong
              (φ₀ : Dmin.R →+* CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) hφ₀).ρ σ) =
            X ^ 2 - C (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X +
              C (ℓ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ))

    (cyc : (q : ℕ) → ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ))
    (πΔ : (q : ℕ) → ((ZMod q)ˣ →* Multiplicative (ZMod (p ^ padicValNat p (q - 1)))))
    (ε : DQ.R →ₐ[𝒪] Dmin.R)
    (ι : MonoidAlgebra 𝒪 (Π i : Fin t, Multiplicative (ZMod (p ^ padicValNat p (qv i - 1)))) →ₐ[𝒪] DQ.R)
    (hcyc : ∀ q : ℕ, q.Prime → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ q = 1 → σ μ = μ ^ ((cyc q σ : ZMod q).val))
    (hπΔ : ∀ q : ℕ, q.Prime → q ≠ p → Function.Surjective (πΔ q))
    (hε : ∃ hε : IsLocalHom (ε : DQ.R →+* Dmin.R),
      (DQ.ρ.baseChangeAlong (ε : DQ.R →+* Dmin.R) hε).IsEquiv Dmin.ρ)
    (hει : ∀ g, ε (ι (MonoidAlgebra.of 𝒪 _ g)) = 1)
    (hin : ∀ i, ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime (qv i) →
      ∃ b : Module.Basis (Fin 2) DQ.R DQ.ρ.V, ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        DQ.ρ.ρ σ (b 0) = ι (MonoidAlgebra.of 𝒪 _ (Pi.mulSingle i (πΔ (qv i) (cyc (qv i) σ)))) • b 0 ∧
        DQ.ρ.ρ σ (b 1) = ι (MonoidAlgebra.of 𝒪 _ (Pi.mulSingle i (πΔ (qv i) (cyc (qv i) σ))⁻¹)) • b 1)

    (hcQ : haveI : NeZero r := ⟨hr.ne_zero⟩; haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hqv i).1.ne_zero⟩
      OpComm N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)))
    (hdc : haveI : NeZero r := ⟨hr.ne_zero⟩; haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hqv i).1.ne_zero⟩
      DiaComm N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)))

    (L : Type) [AddCommGroup L] [Module (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) L] [Module 𝒪 L]
    [IsScalarTower 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) L] [Module.Finite 𝒪 L]
    (lamL : haveI : NeZero r := ⟨hr.ne_zero⟩; haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hqv i).1.ne_zero⟩
      ML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ →ₗ[𝒪] L)
    (hlamT : haveI : NeZero r := ⟨hr.ne_zero⟩; haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hqv i).1.ne_zero⟩
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ level N r qv)
        (x : ML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ),
        lamL ((MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL) :
            (heckeData N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ).FreeAlg) • x) =
          CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ
            (CuspForm.heckeAlgebra.T hℓ (not_dvd_of_not_dvd_level N r qv hℓL) hℓS) • lamL x)
    (hlamD : haveI : NeZero r := ⟨hr.ne_zero⟩; haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hqv i).1.ne_zero⟩
      ∀ u ∈ HR N r qv, ∀ x : ML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ,
        lamL (diaML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ hdc u x) = lamL x) :
    haveI : NeZero r := ⟨hr.ne_zero⟩
    haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hqv i).1.ne_zero⟩
    ∃ (κ : Delta qv p ≃* Delta qv p)
      (ψ : DQ.R →ₐ[𝒪] Module.End 𝒪 (ML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ)),
      (∀ u ∈ HR N r qv,
        ψ (ι (MonoidAlgebra.of 𝒪 _ (κ (piQ N r qv p (fun i => πΔ (qv i)) u)))) =
          diaML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ hdc u) ∧
      (∀ (x : DQ.R) (m : ML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ),
        lamL (ψ x m) = φ₀ (ε x) • lamL m) := by sorry
