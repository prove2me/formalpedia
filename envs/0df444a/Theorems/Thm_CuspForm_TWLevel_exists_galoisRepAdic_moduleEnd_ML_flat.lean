-- Prove2me | Theorems.Thm_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_flat
-- name    : CuspForm.TWLevel.exists_galoisRepAdic_moduleEnd_ML_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/b1dba95c-ceb5-5522-b034-2de1021c11fe
-- title:
--   Galois representation over the Taylor–Wiles Hecke ring acting on M_Q
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring of characteristic zero with finite residue field $k$, and let $p$ be an odd prime lying in its maximal ideal. Let $\bar\rho$ be a two-dimensional residual representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over $k$ (trivial on the absolute Galois group of some number field) which is absolutely irreducible, i.e. irreducible after base change to $\overline{k}$. Let $S_{\min}\subseteq S$ be finite sets of primes with $p\in S_{\min}$, such that a prime $q\neq p$ lies in $S_{\min}$ exactly when $\bar\rho$ is ramified at $q$, and such that for $q\in S_{\min}$, $q\neq p$, the adic representation [`GaloisRepAdic.ofResidualGaloisRep`](def/GaloisRep_Adic.html#L196) $\bar\rho$ has characteristic polynomial $(X-1)^2$ on every inertia group at $q$. Let $N\neq 0$ be squarefree, prime to $p$, with every prime divisor in $S$, divisible by every prime of $S_{\min}$ other than $p$, and with every prime divisor $\neq p$ lying in $S_{\min}$. Let $r\geq 5$ be a prime with $r\notin S$, $r\nmid Np$, $p\nmid r-1$, and $\operatorname{tr}\bar\rho(\sigma)^2\neq (r+1)^2$ for every Frobenius $\sigma$ at every valuation subring of $\overline{\mathbb Q}$ over $r$. Assume the weight-two cusp forms for $\Gamma_0(N)$ are spanned over $\mathbb C$ by those with integral $q$-expansion coefficients, and let $\theta$ be a ring homomorphism from the Hecke algebra [`CuspForm.heckeAlgebra N 2 S`](def/CuspForm_HeckeAlgebra.html#L18) to $k$ with $\operatorname{charpoly}\bar\rho(\mathrm{Frob}_\ell)=X^2-\theta(T_\ell)X+\ell$ for all primes $\ell\nmid N$, $\ell\notin S$. Let $q_0,\dots,q_{t-1}$ be pairwise distinct primes outside $S$ with $p\mid q_i-1$, and let $\alpha_i\in k$ satisfy $\alpha_i^2-\theta(T_{q_i})\alpha_i+q_i=0$ and $2\alpha_i\neq\theta(T_{q_i})$. Let $\mathrm{cyc}_q$ be homomorphisms to $(\mathbb Z/q)^\times$ realising the mod-$q$ cyclotomic character ($\sigma\mu=\mu^{\mathrm{cyc}_q(\sigma)}$ for $\mu^q=1$, $q$ prime), and $\pi^\Delta_q\colon(\mathbb Z/q)^\times\to\mathbb Z/p^{v_p(q-1)}$ homomorphisms that are surjective for $q\neq p$. Write $L=N(\prod_i q_i)r$, $H_R$ for the kernel of $(\mathbb Z/L)^\times\to(\mathbb Z/r)^\times$, $\pi_Q$ for the product of the $\pi^\Delta_{q_i}$ on $(\mathbb Z/L)^\times$, $H_Q=H_R\cap\ker\pi_Q$, and $M_Q$ for the localisation of $H^1(L,H_Q,\mathcal O)$ at the complement of the kernel of the map from $\mathcal O[\,T_\ell,U_i\,]$ to $k$ sending $T_\ell\mapsto\theta(T_\ell)$ and $U_i\mapsto\alpha_i$; assume the operators $T_\ell$, $U_i$ on $H^1(L,H_Q,\mathcal O)$ commute with each other (`OpComm`) and with all diamond operators (`DiaComm`). Then there exist a commutative local Noetherian ring $\mathbb T$, complete for its maximal-adic topology, which is an $\mathcal O$-algebra via a local homomorphism making it a finite $\mathcal O$-module and inducing a surjection $\mathcal O\to\mathbb T/\mathfrak m_{\mathbb T}$, together with an $\mathcal O$-algebra homomorphism $\mathrm{act}\colon\mathbb T\to\operatorname{End}_{\mathcal O}(M_Q)$, a homomorphism $\mathrm{dia}\colon\Delta_Q=\prod_i\mathbb Z/p^{v_p(q_i-1)}\to\mathbb T^\times$, multiplicative automorphisms $\kappa_i$ of $\mathbb Z/p^{v_p(q_i-1)}$, and a representation $\rho$ of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on a free rank-two $\mathbb T$-module, continuous for the adic topology, such that: $\rho$ satisfies [`GaloisRep.flatCondition`](def/GaloisRep_Flat.html#L47) for $(\mathcal O,p,S_{\min}\cup\{q_i\})$, that is $\det\rho$ is cyclotomic modulo the powers of $p$, $\rho$ is flat at $p$ in the sense of `IsFlatAt`, and $\rho$ is unramified outside $S_{\min}\cup\{q_i\}$, and moreover inertia at each prime $q\in S_{\min}$ with $q\neq p$ has characteristic polynomial $(X-1)^2$; the residual representation of $\rho$ is isomorphic to the base change of $\bar\rho$ along $\mathrm{ResidueField}\,\mathcal O\to\mathrm{ResidueField}\,\mathbb T$; for every $u\in H_R$ one has $\mathrm{act}(\mathrm{dia}(\pi_Q(u)))=\mathrm{dia}_{M_Q}(u)$; for every prime $\ell\notin S$ with $\ell\nmid L$ and every Frobenius $\sigma$ at $\ell$ there is $u\in H_R$ with $\mathrm{act}(\operatorname{tr}\rho(\sigma))x=T_\ell\cdot\mathrm{dia}_{M_Q}(u)x$ for all $x\in M_Q$; and for each $i$ and each valuation subring over $q_i$ there is a $\mathbb T$-basis $b_0,b_1$ of $\rho$ in which every element $\sigma$ of inertia acts diagonally by $\mathrm{dia}$ of the $i$-th component $\kappa_i(\pi^\Delta_{q_i}(\mathrm{cyc}_{q_i}(\sigma)))$ and its inverse.
--
--   This is the construction, in the Taylor–Wiles argument, of the Hecke ring $\mathbb T_Q$ of the auxiliary level $L=N(\prod q_i)r$ together with its two-dimensional Galois representation, twisted so as to have cyclotomic determinant, its diamond character on $\Delta_Q$ and its tautological action on the localised cohomology module $M_Q$. It is the input to the construction of the surjection from the relevant deformation ring onto $\mathbb T_Q$ in [`CuspForm.TWLevel.exists_algHom_deformationRing_moduleEnd_ML_flat`](thm.html#CuspForm.TWLevel.exists_algHom_deformationRing_moduleEnd_ML_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_flat.lean

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_TWLevelHeckeModule
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

theorem CuspForm.TWLevel.exists_galoisRepAdic_moduleEnd_ML_flat
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

    (hpN : ¬ p ∣ N)

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
    (hqv : ∀ i, (qv i).Prime ∧ qv i ∉ S ∧ p ∣ qv i - 1)
    (α : Fin t → ResidueField 𝒪)
    (hα : ∀ i, α i ^ 2 - θ (CuspForm.heckeAlgebra.T (hqv i).1
        (fun h => (hqv i).2.1 (hNS _ (hqv i).1 h)) (hqv i).2.1) * α i + (qv i : ResidueField 𝒪) = 0 ∧
      2 * α i ≠ θ (CuspForm.heckeAlgebra.T (hqv i).1 (fun h => (hqv i).2.1 (hNS _ (hqv i).1 h)) (hqv i).2.1))

    (cyc : (q : ℕ) → ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ))
    (πΔ : (q : ℕ) → ((ZMod q)ˣ →* Multiplicative (ZMod (p ^ padicValNat p (q - 1)))))
    (hcyc : ∀ q : ℕ, q.Prime → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ q = 1 → σ μ = μ ^ ((cyc q σ : ZMod q).val))
    (hπΔ : ∀ q : ℕ, q.Prime → q ≠ p → Function.Surjective (πΔ q))

    (hcQ : haveI : NeZero r := ⟨hr.ne_zero⟩; haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hqv i).1.ne_zero⟩
      OpComm N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)))
    (hdc : haveI : NeZero r := ⟨hr.ne_zero⟩; haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hqv i).1.ne_zero⟩
      DiaComm N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i))) :
    haveI : NeZero r := ⟨hr.ne_zero⟩
    haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hqv i).1.ne_zero⟩
    ∃ (𝕋 : Type) (_ : CommRing 𝕋) (_ : IsLocalRing 𝕋) (_ : IsNoetherianRing 𝕋)
      (_ : IsAdicComplete (maximalIdeal 𝕋) 𝕋) (_ : Algebra 𝒪 𝕋) (_ : IsLocalHom (algebraMap 𝒪 𝕋))
      (_ : Module.Finite 𝒪 𝕋),
      Function.Surjective (residue 𝕋 ∘ algebraMap 𝒪 𝕋) ∧
      ∃ (act : 𝕋 →ₐ[𝒪] Module.End 𝒪 (ML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ))
        (dia : Delta qv p →* 𝕋ˣ)
        (κ : ∀ i : Fin t, Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))) ≃*
          Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
        (ρ : GaloisRepAdic 𝕋),

        (GaloisRep.flatCondition 𝒪 p (Smin ∪ Finset.univ.image qv) ρ ∧
          ∀ q ∈ Smin, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q) ∧

        ρ.residual.IsEquiv (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 𝕋))) ∧

        (∀ u ∈ HR N r qv, act ((dia (piQ N r qv p (fun i => πΔ (qv i)) u) : 𝕋ˣ) : 𝕋) =
          diaML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ hdc u) ∧

        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ level N r qv),
          ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
              ∃ u ∈ HR N r qv, ∀ x : ML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ,
                act (ρ.trace σ) x =
                  (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL) :
                    (heckeData N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ).FreeAlg) •
                    diaML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p fun i => πΔ (qv i)) θ α hcQ hdc u x) ∧

        (∀ i, ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime (qv i) →
          ∃ b : Module.Basis (Fin 2) 𝕋 ρ.V, ∀ σ ∈ P.inertiaSubgroupIn ℚ,
            ρ.ρ σ (b 0) = ((dia (Pi.mulSingle i (κ i (πΔ (qv i) (cyc (qv i) σ)))) : 𝕋ˣ) : 𝕋) • b 0 ∧
            ρ.ρ σ (b 1) = (((dia (Pi.mulSingle i (κ i (πΔ (qv i) (cyc (qv i) σ)))))⁻¹ : 𝕋ˣ) : 𝕋) • b 1) := by sorry
