-- Prove2me | Theorems.Thm_CerednikDrinfeld_TwoPlaceTorsionDatum_W_le_invariants_of_goodReductionOutside_of_span_eq_top
-- name    : CerednikDrinfeld.TwoPlaceTorsionDatum.W_le_invariants_of_goodReductionOutside_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/640b9cf9-21f9-5265-aca9-c7b51595bcaa
-- title:
--   Inertia invariance of W_𝔪 at the second place
-- statement:
--   Fix an odd prime $p$ and finite types $E_1,V_1,E_2,V_2$. Let $D_i$ be degeneracy data on $(E_i,V_i)$ (maps $a,b\colon E_i\to V_i$ and weights $w\colon E_i\to\mathbb Z_{>0}$), let $H_i$ be Hecke data for $D_i$ (commuting integral matrices on $E_i$ and on $V_i$, equivariant for the two pushforwards outside a finite set of primes and stabilising the ribbon kernel), and let $A_1,A_2$ be valuation subrings of $\overline{\mathbb Q}$. Let $\mathcal J$ be a two-place $p$-torsion datum for these data: a finite abelian group $T$ killed by $p$, a ring homomorphism from $\mathbb T=\mathbb Z[X_\ell:\ell\text{ prime}]$ to $\operatorname{End}_{\mathbb Z}T$, a homomorphism $\mathrm{gal}$ from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to the additive automorphisms of $T$ commuting with the Hecke action and trivial on the subgroup fixing some finite extension of $\mathbb Q$, together with subgroups $\mathrm{toric}_i\subseteq T$ identified with $\operatorname{Hom}(\mathrm{ribbonKernel}(D_i),\mathbb Z/p)$ and specialisation maps $\mathrm{sp}_i$ from the $A_i$-inertia invariants of $T$ to the ribbon component group of $D_i$. Assume, for some $M\in\mathbb N$, that the datum $\mathcal J.\mathrm{fst}$ at the first place has good reduction outside $M$: for every prime $\ell\nmid M$ and every valuation subring $B$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $B$, the image of the inertia subgroup of $B$ acts trivially on $T$, and for every $\sigma$ which is a Frobenius at $B$ for $\ell$ (acting as $x\mapsto x^\ell$ on the residue field) one has $\sigma^2t-X_\ell\,\sigma t+\ell t=0$ for all $t\in T$. Let $\mathfrak m\subseteq\mathbb T$ be a maximal ideal with $p\in\mathfrak m$, let $F$ be a finite field with a ring homomorphism $\iota\colon F\to\mathbb T/\mathfrak m$, and let $\rho$ be a multiplicative homomorphism from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $2\times2$ matrices over $F$. Assume: (i) there is a finite set $S$ of natural numbers such that every prime outside $S$ fails to divide $M$ and such that for every prime $\ell\notin S$, every valuation subring $A$ with $\ell$ a non-unit of $A$ and every Frobenius $\sigma$ at $A$ for $\ell$, the class of $X_\ell$ modulo $\mathfrak m$ is the trace and the class of $\ell$ modulo $\mathfrak m$ is the determinant of $\iota$ applied entrywise to $\rho(\sigma)$; (ii) the $\mathbb T/\mathfrak m$-span of all these matrices $\iota(\rho(\sigma))$ is the whole matrix algebra; (iii) $\rho$ is trivial on the subgroup fixing some finite extension of $\mathbb Q$; (iv) $\rho(\sigma)=1$ for every $\sigma$ in the image in $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A_2$. Then the subgroup $\mathcal J.\mathrm{snd}.W(\mathfrak m)$ of $T$ is contained in the invariants of $\mathcal J.\mathrm{snd}$, that is, in the intersection over all $\sigma$ in the inertia subgroup of $A_2$ of the kernels of $\mathrm{gal}(\sigma)-\mathrm{id}_T$.
--
--   This is the Galois-theoretic input of Boston–Lenstra–Ribet type in Ribet's level-exchange argument: absolute irreducibility in Burnside form forces the $\mathfrak m$-part of the torsion datum to be built from copies of the residual representation $\rho$, so that unramifiedness of $\rho$ at the second place transfers to the subgroup $W_{\mathfrak m}$. It supplies the inertia-invariance hypothesis for the toric comparison at the datum $\mathcal J.\mathrm{snd}$, and is used in the comparison of ranks of spans of toric monodromy parts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_TwoPlaceTorsionDatum_W_le_invariants_of_goodReductionOutside_of_span_eq_top.lean

import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open CerednikDrinfeld

theorem CerednikDrinfeld.TwoPlaceTorsionDatum.W_le_invariants_of_goodReductionOutside_of_span_eq_top
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁]
    [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}
    (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    {M : ℕ} (hgood : 𝒥.fst.GoodReductionOutside M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : (p : HeckeAlg) ∈ 𝔪)
    (F : Type) [Field F] [Fintype F] (ι : F →+* HeckeAlg ⧸ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
    (hatt : ∃ S : Finset ℕ, (∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
          Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = ((ρ σ).map ι).trace ∧
            Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = ((ρ σ).map ι).det)
    (hspan : Submodule.span (HeckeAlg ⧸ 𝔪)
      (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => (ρ σ).map ι) = ⊤)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (hunr : ∀ σ ∈ A₂.inertiaSubgroupIn ℚ, ρ σ = 1) :
    𝒥.snd.W 𝔪 ≤ 𝒥.snd.invariants := by sorry
