-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_exists_ringHom_quotient_forall_coe_apply_eq_evalAt
-- name    : AlgebraicCurve.NodeAnnulusEngine.exists_ringHom_quotient_forall_coe_apply_eq_evalAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/269faac7-e861-5c22-89f4-99bcd18b6408
-- title:
--   Evaluation at a place gives a C-point mathcal N₀/𝔭 → A
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, and $F$ a field, essentially of finite type over $L$, which is a curve over $L$ in the sense of `IsCurveOver` (principal divisors of degree zero exist for all nonzero functions, every place has residue field finite over $L$, and $\Omega[F\!\restriction\! L]$ is free of rank one over $F$); places are valuation subrings of $F$ containing $L$, proper and principal ideal rings. Let $S$ be a set of places all of which are rational, i.e. $L$ surjects onto the residue field, so that the evaluation $P.\mathrm{evalAt}$ (the inverse image in $L$ of the residue, and $0$ off the valuation subring) is defined. Let $\mathcal N_0 \subseteq F$ be a local Noetherian subring such that membership of a place $P$ in $S$ is equivalent to: $\mathcal N_0$ lies in the valuation subring of $P$, and every non-unit of $\mathcal N_0$ has value at $P$ lying in the maximal ideal of $A$. Further hypotheses are assumed and summarised here: $\mathcal N_0$ generates $F$ after clearing a denominator by $L$-linear combinations; a subring $C \subseteq A$ with $C \subseteq \mathcal N_0$ via $L \to F$, a nonzero $\varpi \in C$ cutting out the kernel of the residue map of $A$ on $C$, $C$ a discrete valuation domain with $A$ algebraic over it; linear disjointness of $\mathcal N_0$ from $L$ over $C$; a power-divisibility condition in $A$; every element of $\mathcal N_0$ is a constant from $C$ plus a non-unit; and a crossing presentation, namely a complete discrete valuation domain $W$ with irreducible $\pi$, a map $\sigma : W \to \widehat{\mathcal N_0}$ sending $\pi$ to the image of $\varpi$, an integer $E \ge 1$ and an isomorphism of the maximal-ideal-adic completion $\widehat{\mathcal N_0}$ with $W[[X_0,X_1]]/(X_0X_1 - \pi^E)$ carrying $\sigma$ to the constants. Finally let $\mathfrak p$ be a nonzero prime of $\mathcal N_0$ not containing the constant $\varpi$, and $P \in S$ a place with $P.\mathrm{evalAt}(g) = 0 \iff g \in \mathfrak p$ for $g \in \mathcal N_0$. The conclusion is that there is a ring homomorphism $\varphi : \mathcal N_0/\mathfrak p \to A$ fixing the constants, $\varphi(\overline{c}) = c$ for $c \in C$, and satisfying $\varphi(\overline g) = P.\mathrm{evalAt}(g)$ in $L$ for every $g \in \mathcal N_0$. The proof uses only the rationality of $P$, the characterisation of $S$, the decomposition of elements of $\mathcal N_0$ as a constant plus a non-unit, and the identification of $\mathfrak p$ as the vanishing locus of $P$; the remaining hypotheses (generation, linear disjointness, power divisibility, algebraicity over $C$, the properties of $\varpi$, the crossing presentation.
--
--   This is the reduction map of the place–model dictionary for a node: a place of $F/L$ centred at a horizontal prime $\mathfrak p$ of the node ring $\mathcal N_0$ yields a $C$-algebra point of $\mathcal N_0/\mathfrak p$ with values in the valuation ring $A$. It is used by [`AlgebraicCurve.NodeAnnulusEngine.nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero`](thm.html#AlgebraicCurve.NodeAnnulusEngine.nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero), where such points are matched against homomorphisms out of the quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_exists_ringHom_quotient_forall_coe_apply_eq_evalAt.lean

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

theorem AlgebraicCurve.NodeAnnulusEngine.exists_ringHom_quotient_forall_coe_apply_eq_evalAt
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
    (𝔭 : Ideal ↥𝒩₀) [𝔭.IsPrime] (h𝔭0 : 𝔭 ≠ ⊥) (h𝔭ϖ : (⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀) ∉ 𝔭)
    (P : Place L F) (hP : P ∈ S) (hP𝔭 : ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭) :
    ∃ φ : (↥𝒩₀ ⧸ 𝔭) →+* ↥A,
      (∀ c : ↥C, φ (Ideal.Quotient.mk 𝔭 ⟨algebraMap L F (c : L), hCmem c c.2⟩) = ⟨(c : L), hC c c.2⟩) ∧
      ∀ g : ↥𝒩₀, ((φ (Ideal.Quotient.mk 𝔭 g) : ↥A) : L) = P.evalAt (g : F) := by sorry
