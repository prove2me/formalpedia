-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_eq_of_forall_evalAt_eq_of_forall_iff_evalAt_eq_zero
-- name    : AlgebraicCurve.NodeAnnulusEngine.eq_of_forall_evalAt_eq_of_forall_iff_evalAt_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/91db4c26-41c3-5722-b056-7c612f439391
-- title:
--   A place of S over a horizontal prime is determined by its values on mathcal N₀
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, and $F$ an $L$-algebra which is a field, of essentially finite type over $L$ and a curve over $L$ in the sense that principal divisors of degree zero exist for all nonzero elements, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one. Let $S$ be a set of places of $F/L$ (each given by a valuation subring of $F$ containing $L$, proper, and a principal ideal ring), all of whose members are rational, i.e. $L$ surjects onto the residue field, so that $P.\mathrm{evalAt}$ is defined; and let $\mathcal N_0 \subseteq F$ be a local Noetherian subring. Assume: $S$ consists exactly of those places $P$ with $\mathcal N_0$ inside the valuation ring of $P$ and with $P.\mathrm{evalAt}(f) \in A$ lying in the maximal ideal of $A$ for every non-unit $f$ of $\mathcal N_0$; every $f \in F$ satisfies $f b = \sum_i c_i a_i$ for some nonzero $b \in \mathcal N_0$, finitely many $c_i \in L$ and $a_i \in \mathcal N_0$. Let $C \subseteq L$ be a subring contained in $A$ whose image lies in $\mathcal N_0$, which is a domain and a discrete valuation ring, with $\varpi \in C$ nonzero such that for $d \in C$ the residue of $d$ in the residue field of $A$ vanishes iff $\varpi \mid d$ in $C$, and with every element of $A$ algebraic over $C$. Assume further: any family $c : \mathrm{Fin}\,n \to L$ linearly independent over $C$ satisfies that $\sum_i c_i a_i = 0$ forces $a_i = 0$ for all $a_i \in \mathcal N_0$; for $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$, $b$ divides some power of $a$; every $g \in \mathcal N_0$ becomes a non-unit after subtracting the image of a suitable element of $C$. Let $W$ be a complete discrete valuation ring with $\pi \in W$ irreducible, $\sigma : W \to \widehat{\mathcal N_0}$ a ring homomorphism sending $\pi$ to the image of $\varpi$ in the completion of $\mathcal N_0$ at its maximal ideal, $E \geq 1$, and $\iota$ a ring isomorphism from $\widehat{\mathcal N_0}$ to $\mathrm{MvPowerSeries}(\mathrm{Fin}\,2, W)/(X_0X_1 - \pi^E)$ carrying $\sigma(o)$ to the class of the constant series $o$ for every $o \in W$. Finally let $\mathfrak p$ be a nonzero prime ideal of $\mathcal N_0$ not containing the image of $\varpi$, and let $P, P' \in S$ be such that for $g \in \mathcal N_0$ one has $P.\mathrm{evalAt}(g) = 0$ exactly when $g \in \mathfrak p$, and $P.\mathrm{evalAt}(g) = P'.\mathrm{evalAt}(g)$ for all $g \in \mathcal N_0$. Then $P = P'$.
--
--   This is the injectivity statement for the map sending a place in the node frame to its tuple of values on $\mathcal N_0$: a place centred at a horizontal prime $\mathfrak p$ of the local ring $\mathcal N_0$ of the node is pinned down by the evaluation homomorphism $g \mapsto g(P)$. It is used by [`AlgebraicCurve.NodeAnnulusEngine.nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero`](thm.html#AlgebraicCurve.NodeAnnulusEngine.nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero) to identify places over $\mathfrak p$ with ring homomorphisms out of the quotient $\mathcal N_0/\mathfrak p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_eq_of_forall_evalAt_eq_of_forall_iff_evalAt_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.UVCrossingModel
open IsLocalRing

theorem AlgebraicCurve.NodeAnnulusEngine.eq_of_forall_evalAt_eq_of_forall_iff_evalAt_eq_zero
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
    (P P' : Place L F) (hP : P ∈ S) (hP' : P' ∈ S) (hP𝔭 : ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭)
    (h : ∀ g : ↥𝒩₀, P.evalAt (g : F) = P'.evalAt (g : F)) :
    P = P' := by sorry
