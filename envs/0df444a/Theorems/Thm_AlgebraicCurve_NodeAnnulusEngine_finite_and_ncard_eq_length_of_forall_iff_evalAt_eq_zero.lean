-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_finite_and_ncard_eq_length_of_forall_iff_evalAt_eq_zero
-- name    : AlgebraicCurve.NodeAnnulusEngine.finite_and_ncard_eq_length_of_forall_iff_evalAt_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/c92db754-c794-5cc5-9616-1d353ff80df6
-- title:
--   Counting places above a horizontal prime by length(mathcal N₀/(𝔭+varpi))
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A$ a valuation subring of $L$, and $F$ an extension field of $L$ that is a curve over $L$ (principal divisors, $L$-finite residue fields at all places, $\Omega_{F/L}$ free of rank one) and essentially of finite type over $L$. Let $S$ be a set of places of $F/L$ (valuation subrings of $F$ containing $L$, proper, with principal ideals), each member rational, i.e. $L$ surjects onto its residue field; let $\mathcal N_0\subseteq F$ be a local Noetherian subring. Assume: $P\in S$ exactly when $\mathcal N_0\subseteq P$ and every non-unit of $\mathcal N_0$ has its value $P.\mathrm{evalAt}$ in the maximal ideal of $A$; every $f\in F$ satisfies $fb=\sum_i c_i a_i$ with $0\neq b\in\mathcal N_0$, $c_i\in L$, $a_i\in\mathcal N_0$; a subring $C\subseteq A\cap L$ with $C\subseteq\mathcal N_0$ in $F$, a discrete valuation domain, with $\varpi\in C$ nonzero generating the contraction to $C$ of the maximal ideal of $A$; every element of $A$ algebraic over $C$; $C$-linearly independent coefficients force vanishing of the $a_i$ in a vanishing combination; for $a,b\in A$ with $a$ in the maximal ideal and $b\neq0$, $b\mid a^n$ for some $n$; every $g\in\mathcal N_0$ is non-unit after subtracting some element of $C$. Let $W$ be a complete discrete valuation domain, $\pi$ irreducible, $\sigma:W\to\widehat{\mathcal N_0}$ a ring homomorphism sending $\pi$ to $\varpi$, $E\geq1$, and $\iota:\widehat{\mathcal N_0}\simeq W[[U,V]]/(UV-\pi^E)$ a ring isomorphism carrying $\sigma$ to the constants. Let $\mathfrak p\subset\mathcal N_0$ be a nonzero prime with $\varpi\notin\mathfrak p$. Then $\{P\in S:\ \forall g\in\mathcal N_0,\ P.\mathrm{evalAt}(g)=0\iff g\in\mathfrak p\}$ is finite and its cardinality, as an element of $\mathbb N_\infty$, equals the $\mathcal N_0$-module length of $\mathcal N_0/(\mathfrak p+\varpi\mathcal N_0)$.
--
--   This is the place-theoretic half of the branch count at a node: the places of $S$ centred at a horizontal prime $\mathfrak p$ of the rational node ring are counted by the intersection multiplicity at the node of the closure of $\mathfrak p$ with the special fibre $\varpi=0$. It is used by the companion statement that evaluates the same number as a sum of $W$-ranks over the branches of the crossing model $W[[U,V]]/(UV-\pi^E)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_finite_and_ncard_eq_length_of_forall_iff_evalAt_eq_zero.lean

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

theorem AlgebraicCurve.NodeAnnulusEngine.finite_and_ncard_eq_length_of_forall_iff_evalAt_eq_zero
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
    {P : Place L F | P ∈ S ∧ ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭}.Finite ∧
    (({P : Place L F | P ∈ S ∧ ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭}.ncard : ℕ) : ℕ∞) =
      Module.length ↥𝒩₀ (↥𝒩₀ ⧸ (𝔭 ⊔ Ideal.span {(⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀)})) := by sorry
