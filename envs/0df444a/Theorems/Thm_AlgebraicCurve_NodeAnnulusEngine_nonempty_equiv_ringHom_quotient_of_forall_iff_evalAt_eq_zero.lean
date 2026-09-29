-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero
-- name    : AlgebraicCurve.NodeAnnulusEngine.nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/37578bce-ce25-5729-b5aa-715364740591
-- title:
--   Places over a horizontal prime as C-points of mathcal N₀/𝔭
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, and $F/L$ a field extension which is a curve over $L$ (principal divisors exist, all residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type. Let $S$ be a set of places of $F/L$ — valuation subrings of $F$ containing $L$, proper, with principal ideals — each of which is rational, i.e. $L$ surjects onto its residue field, and let $\mathcal N_0 \subseteq F$ be a Noetherian local subring. The hypotheses are: $S$ consists exactly of the places $P$ whose valuation ring contains $\mathcal N_0$ and at which every non-unit of $\mathcal N_0$ takes a value lying in the maximal ideal of $A$; every $f \in F$ satisfies $fb = \sum_i c_i a_i$ with $0 \neq b \in \mathcal N_0$, $c_i \in L$, $a_i \in \mathcal N_0$; a subring $C \subseteq A \cap L$ mapping into $\mathcal N_0$, which is a discrete valuation domain with a nonzero element $\varpi$ whose multiples in $C$ are exactly the elements with zero residue in $A$; every element of $A$ is algebraic over $C$; $L$-combinations of elements of $\mathcal N_0$ with $C$-linearly independent coefficients vanish only trivially; for $a$ in the maximal ideal of $A$ and $b \neq 0$ in $A$, $b$ divides a power of $a$; every $g \in \mathcal N_0$ differs from some element of $C$ by a non-unit; and a complete discrete valuation domain $W$ with irreducible $\pi$, a ring map $\sigma : W \to \widehat{\mathcal N_0}$ (completion at the maximal ideal) sending $\pi$ to the image of $\varpi$, an $E \geq 1$ and a ring isomorphism $\iota : \widehat{\mathcal N_0} \cong W[[X_0,X_1]]/(X_0X_1 - \pi^E)$ carrying $\sigma$ to the constants. Finally let $\mathfrak p \subset \mathcal N_0$ be a nonzero prime not containing the image of $\varpi$. The conclusion asserts that there exists a bijection between the set of places $P \in S$ for which the values $P.\mathrm{evalAt}(g)$, $g \in \mathcal N_0$, vanish exactly on $\mathfrak p$, and the set of ring homomorphisms $\varphi : \mathcal N_0/\mathfrak p \to A$ with $\varphi(c \bmod \mathfrak p) = c$ for all $c \in C$; the statement is the mere non-emptiness of the type of such bijections, no particular map being named.
--
--   This is the bridge step of the place–model dictionary for a node: the places of $F$ in the distinguished set $S$ lying over a horizontal prime $\mathfrak p$ of the local ring $\mathcal N_0$ are counted by the $C$-algebra homomorphisms $\mathcal N_0/\mathfrak p \to A$, so that reduction-of-points questions become a question about homomorphisms into the valuation ring of constants. It is used by [`AlgebraicCurve.NodeAnnulusEngine.finite_and_ncard_eq_length_of_forall_iff_evalAt_eq_zero`](thm.html#AlgebraicCurve.NodeAnnulusEngine.finite_and_ncard_eq_length_of_forall_iff_evalAt_eq_zero), where the resulting cardinality is identified with a length.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero.lean

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

theorem AlgebraicCurve.NodeAnnulusEngine.nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero
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
    Nonempty ({P : Place L F // P ∈ S ∧ ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭} ≃
      {φ : (↥𝒩₀ ⧸ 𝔭) →+* ↥A //
        ∀ c : ↥C, φ (Ideal.Quotient.mk 𝔭 ⟨algebraMap L F (c : L), hCmem c c.2⟩) = ⟨(c : L), hC c c.2⟩}) := by sorry
