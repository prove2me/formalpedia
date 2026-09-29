-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel
-- name    : AlgebraicCurve.NodeAnnulusEngine.finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/6cff7093-9d60-585d-86f9-9de4cfc2913a
-- title:
--   Node places count horizontal zeros in a uv-crossing model
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A\subseteq L$ a valuation subring, and $F$ a field, an $L$-algebra that is essentially of finite type and satisfies `IsCurveOver L F`: every nonzero element of $F$ has a degree-zero divisor whose value at each place is the order of that element, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank $1$ over $F$. Here a place is a valuation subring of $F$ containing $L$, distinct from $F$, and a principal ideal ring; $\mathrm{ord}_P$ is minus the logarithm of the associated adic valuation. Let $S$ be a set of places, each rational (the map $L\to$ residue field is surjective), and $\mathcal N_0\subseteq F$ a Noetherian local subring. The hypotheses are: $P\in S$ if and only if $\mathcal N_0$ lies in $P$'s valuation ring and every non-unit of $\mathcal N_0$ evaluates at $P$ into the maximal ideal of $A$; every $f\in F$ satisfies $fb=\sum_i c_i a_i$ for some $0\ne b\in\mathcal N_0$, $c_i\in L$, $a_i\in\mathcal N_0$; a subring $C\subseteq A\cap L$, a domain and discrete valuation ring, mapping into $\mathcal N_0$, with $\varpi\in C$ nonzero whose multiples are exactly the elements of $C$ with zero residue in $A$; every element of $A$ is algebraic over $C$; $C$-linearly independent families $c_i$ in $L$ admit no nontrivial relation $\sum_i c_ia_i=0$ with $a_i\in\mathcal N_0$; for $a$ in the maximal ideal of $A$ and $b\ne0$ in $A$, $b$ divides a power of $a$; and every $g\in\mathcal N_0$ differs from some element of $C$ by a non-unit. Let $W$ be a complete discrete valuation domain, $\pi$ irreducible in $W$, $\sigma:W\to\widehat{\mathcal N_0}$ a ring homomorphism sending $\pi$ to $\varpi$, where $\widehat{\mathcal N_0}$ is the adic completion of $\mathcal N_0$ at its maximal ideal, $E\ge1$, and $\iota:\widehat{\mathcal N_0}\xrightarrow{\sim}R:=W[[X_0,X_1]]/(X_0X_1-\pi^E)$ a ring isomorphism carrying $\sigma(o)$ to the constant $o$ for all $o\in W$. Then for every nonzero $f\in\mathcal N_0$ the set of $P\in S$ with $\mathrm{ord}_P(f)\ne0$ is finite, and, in $\mathbb N_\infty$, $\sum_{P\in S}\mathrm{ord}_P(f)$ (each term taken as a natural number) equals the sum over primes $Q$ of $R$ with $Q\ne0$ and the constant $\pi\notin Q$ of $\operatorname{rank}_W(R/Q)$ times the length of the localisation of $R/(\iota f)$ at $Q$ over $R_Q$.
--
--   This is the dictionary between the $L$-rational places of the curve specialising into a node and the horizontal primes of the associated $uv$-crossing model $W[[X_0,X_1]]/(X_0X_1-\pi^E)$: the degree of the divisor of a node-ring function on those places equals the number of zeros of its image, counted with multiplicity and with residue degree over $W$, on the generic fibre of the model. It is used in the layered form of the statement, which splits off the contribution of the residue of the function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.NodeAnnulusEngine.finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))

    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)

    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (f : ↥𝒩₀) (hf0 : f ≠ 0) :
    {P : Place L F | P ∈ S ∧ P.ord (f : F) ≠ 0}.Finite ∧
    ((∑ᶠ P ∈ S, (P.ord (f : F)).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥𝒩₀ _ f)})) := by sorry
