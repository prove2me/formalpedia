-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_finsum_finrank_quotient_eq_length_of_comap_eq
-- name    : AlgebraicCurve.NodeAnnulusEngine.finsum_finrank_quotient_eq_length_of_comap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/9755d8ed-66ea-5135-8418-fa010b6201da
-- title:
--   Total W-rank of branches over a horizontal prime
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A$ a valuation subring of $L$, and $F$ a field, essentially of finite type over $L$, which is a curve over $L$ in the project's sense: principal divisors of degree zero exist for all nonzero elements, every place has residue field finite over $L$, and $\Omega[F/L]$ is free of rank one over $F$. Let $S$ be a set of places of $F/L$, each rational (the map from $L$ to its residue field being surjective), and let $\mathcal N_0\subseteq F$ be a local Noetherian subring such that a place $P$ lies in $S$ precisely when $\mathcal N_0$ is contained in the valuation subring of $P$ and every non-unit $f$ of $\mathcal N_0$ has $P.\mathrm{evalAt}(f)\in A$ lying in the maximal ideal of $A$; assume further that every $f\in F$ admits a nonzero $b\in\mathcal N_0$ with $fb$ an $L$-linear combination of finitely many elements of $\mathcal N_0$. Let $C\subseteq L$ be a subring contained in $A$ whose image in $F$ lies in $\mathcal N_0$, a domain and a discrete valuation ring, with $\varpi\in C$ nonzero such that for $d\in C$ the residue of $d$ in the residue field of $A$ vanishes exactly when $d\in\varpi C$; assume every element of $A$ is algebraic over $C$, that families $c_i\in L$ linearly independent over $C$ satisfy $\sum_i c_i a_i=0\Rightarrow a_i=0$ for $a_i\in\mathcal N_0$, that for $a,b\in A$ with $a$ in the maximal ideal and $b\neq 0$ one has $b\mid a^n$ for some $n$, and that every $g\in\mathcal N_0$ becomes a non-unit after subtracting the image of a suitable element of $C$. Let $W$ be a complete discrete valuation domain, $\pi$ an irreducible element of $W$, $E\geq 1$, and let $\sigma:W\to\widehat{\mathcal N_0}$ (adic completion at the maximal ideal) be a ring homomorphism sending $\pi$ to the image of $\varpi$, together with a ring isomorphism $\iota:\widehat{\mathcal N_0}\xrightarrow{\sim} W[[U,V]]/(UV-\pi^E)$ (that is, $\mathrm{MvPowerSeries}\,(\mathrm{Fin}\,2)\,W$ modulo $X_0X_1-C(\pi^E)$) carrying $\sigma(o)$ to the constant $\mathrm{const}\,(\pi^E)\,o$ for every $o\in W$. Finally let $\mathfrak p\subset\mathcal N_0$ be a nonzero prime ideal not containing the image of $\varpi$. Then the sum, over those primes $Q$ of $W[[U,V]]/(UV-\pi^E)$ whose contraction along $\mathcal N_0\to\widehat{\mathcal N_0}\xrightarrow{\iota}W[[U,V]]/(UV-\pi^E)$ equals $\mathfrak p$, of the $W$-ranks $\mathrm{finrank}_W\bigl((W[[U,V]]/(UV-\pi^E))/Q\bigr)$, taken as a finitely supported sum of values in $\mathbb N_\infty$, equals the $\mathcal N_0$-length of $\mathcal N_0/(\mathfrak p+\varpi\mathcal N_0)$.
--
--   This is the model side of the branch count at a node in the place–model dictionary: the total $W$-rank of the branches of the completed local ring lying over a horizontal prime $\mathfrak p$ equals the intersection multiplicity of the closure of $\mathfrak p$ with the special fibre. It feeds the counting statement [`AlgebraicCurve.NodeAnnulusEngine.finite_and_ncard_eq_finsum_finrank_of_forall_iff_evalAt_eq_zero`](thm.html#AlgebraicCurve.NodeAnnulusEngine.finite_and_ncard_eq_finsum_finrank_of_forall_iff_evalAt_eq_zero), and uses the reducedness of the relevant quotients together with the dimension, normality, completeness and freeness properties of the crossing model $W[[U,V]]/(UV-\pi^E)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_finsum_finrank_quotient_eq_length_of_comap_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open IsLocalRing
open ModularCurve
open ModularCurve.UVCrossingModel

theorem AlgebraicCurve.NodeAnnulusEngine.finsum_finrank_quotient_eq_length_of_comap_eq
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
    (𝔭 : Ideal ↥𝒩₀) [𝔭.IsPrime] (h𝔭0 : 𝔭 ≠ ⊥) (h𝔭ϖ : (⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀) ∉ 𝔭) :
    ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Ideal.comap ((ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ →+* UVCrossingModel W (π ^ E)).comp
                (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀))) Q.asIdeal = 𝔭),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) =
      Module.length ↥𝒩₀ (↥𝒩₀ ⧸ (𝔭 ⊔ Ideal.span {(⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀)})) := by sorry
