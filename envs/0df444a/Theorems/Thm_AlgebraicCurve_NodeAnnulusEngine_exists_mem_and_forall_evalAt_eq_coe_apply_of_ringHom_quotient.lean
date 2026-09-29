-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_forall_evalAt_eq_coe_apply_of_ringHom_quotient
-- name    : AlgebraicCurve.NodeAnnulusEngine.exists_mem_and_forall_evalAt_eq_coe_apply_of_ringHom_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/be32292d-2921-5813-be7b-57d9bcef42b8
-- title:
--   Every C-point of mathcal N₀/𝔭 in A is an evaluation
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A\subseteq L$ a valuation subring, and $F$ a field extension of $L$ which is essentially of finite type and a curve over $L$ (principal divisors exist, all residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank one). Let $S$ be a set of places of $F/L$ — valuation subrings of $F$ containing $L$, proper, with principal ideals — all of which are rational, i.e. $L$ surjects onto the residue field, so that $P.\mathrm{evalAt}$ sends an element of the valuation subring to the unique element of $L$ with the same residue, and $0$ elsewhere. Let $\mathcal N_0\subseteq F$ be a local Noetherian subring such that $S$ consists exactly of the places $P$ with $\mathcal N_0$ inside the valuation subring of $P$ and with $P.\mathrm{evalAt}(f)$ lying in the maximal ideal of $A$ for every non-unit $f$ of $\mathcal N_0$; assume every $f\in F$ satisfies $fb=\sum_i c_i a_i$ for some nonzero $b\in\mathcal N_0$, finitely many $c_i\in L$ and $a_i\in\mathcal N_0$. Let $C\subseteq L$ be a subring contained in $A$ whose image in $F$ lies in $\mathcal N_0$, which is a discrete valuation ring with a nonzero $\varpi\in C$ such that an element of $C$ has residue zero in $A$ exactly when it is a multiple of $\varpi$; assume every element of $A$ is algebraic over $C$, that any family in $L$ linearly independent over $C$ remains independent against coefficients in $\mathcal N_0$ (if $\sum_i c_i a_i=0$ with $a_i\in\mathcal N_0$ then all $a_i=0$), that for $a$ in the maximal ideal of $A$ and $b\in A$ nonzero some power $a^n$ is divisible by $b$, and that every $g\in\mathcal N_0$ differs from the image of some element of $C$ by a non-unit. Let $W$ be a complete discrete valuation domain, $\pi\in W$ irreducible, $\sigma:W\to \widehat{\mathcal N_0}$ a ring homomorphism into the completion of $\mathcal N_0$ at its maximal ideal sending $\pi$ to the image of $\varpi$, $E\ge 1$, and $\iota$ a ring isomorphism $\widehat{\mathcal N_0}\cong W[[u,v]]/(uv-\pi^E)$ compatible with the constants, i.e. $\iota(\sigma(o))=\mathrm{const}(\pi^E,o)$ for all $o\in W$. Finally let $\mathfrak p$ be a nonzero prime of $\mathcal N_0$ not containing the image of $\varpi$, and $\varphi:\mathcal N_0/\mathfrak p\to A$ a ring homomorphism which is the identity on the classes of elements of $C$. Then there is a place $P\in S$ whose vanishing locus on $\mathcal N_0$ is exactly $\mathfrak p$, that is $P.\mathrm{evalAt}(g)=0$ iff $g\in\mathfrak p$, and which computes $\varphi$: $P.\mathrm{evalAt}(g)=\varphi(g\bmod\mathfrak p)$ in $L$ for every $g\in\mathcal N_0$.
--
--   This is the surjectivity half of the dictionary between places of $F/L$ lying in the annulus region $S$ and $C$-algebra homomorphisms $\mathcal N_0/\mathfrak p\to A$, for the local ring $\mathcal N_0$ of a node whose completion is a crossing model $W[[u,v]]/(uv-\pi^E)$: every such homomorphism is evaluation at a place centred at $\mathfrak p$. It is used to produce the bijection in [`AlgebraicCurve.NodeAnnulusEngine.nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero`](thm.html#AlgebraicCurve.NodeAnnulusEngine.nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_forall_evalAt_eq_coe_apply_of_ringHom_quotient.lean

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

theorem AlgebraicCurve.NodeAnnulusEngine.exists_mem_and_forall_evalAt_eq_coe_apply_of_ringHom_quotient
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
    (φ : (↥𝒩₀ ⧸ 𝔭) →+* ↥A)
    (hφ : ∀ c : ↥C, φ (Ideal.Quotient.mk 𝔭 ⟨algebraMap L F (c : L), hCmem c c.2⟩) = ⟨(c : L), hC c c.2⟩) :
    ∃ P : Place L F, P ∈ S ∧ (∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭) ∧
      ∀ g : ↥𝒩₀, P.evalAt (g : F) = ((φ (Ideal.Quotient.mk 𝔭 g) : ↥A) : L) := by sorry
