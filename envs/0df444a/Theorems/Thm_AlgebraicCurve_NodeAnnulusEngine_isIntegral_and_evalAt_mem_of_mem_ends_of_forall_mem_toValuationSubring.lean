-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring
-- name    : AlgebraicCurve.NodeAnnulusEngine.isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/ea9b39df-12da-5dea-bcb9-5c31f3873b4e
-- title:
--   Maximum principle at a node: integrality over the node ring
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A\subseteq L$ a valuation subring, and $F$ a field extension of $L$ with `IsCurveOver L F` (principal divisors for all places, each place's residue field finite over $L$, and $\Omega_{F/L}$ free of rank one over $F$) and $F$ essentially of finite type over $L$. Let $S$ be a set of places of $F/L$ — each place being a valuation subring of $F$ containing $L$, proper, and a principal ideal ring — with every $P\in S$ rational, i.e. $L\to\kappa(P)$ surjective. Let $\mathcal N_0\subseteq F$ be a Noetherian local subring such that $S$ consists exactly of the places $P$ with $\mathcal N_0\subseteq\mathcal O_P$ and such that every non-unit $f$ of $\mathcal N_0$ has $P.\mathrm{evalAt}(f)\in\mathfrak m_A$ (where $\mathrm{evalAt}$ is the inverse image in $L$ of the residue of $f$, and $0$ off $\mathcal O_P$), and such that every $f\in F$ satisfies $fb=\sum_i c_i a_i$ for some $0\neq b\in\mathcal N_0$, finitely many $c_i\in L$ and $a_i\in\mathcal N_0$. Let $C\subseteq L$ be a subring contained in $A$ whose image lies in $\mathcal N_0$, which is a discrete valuation ring, with $\varpi\in C$ nonzero such that for $d\in C$ the residue of $d$ in $A$ vanishes iff $\varpi\mid d$ in $C$; assume every element of $A$ is algebraic over $C$, every $C$-linearly independent family $(c_i)$ in $L$ satisfies: $\sum_i c_i a_i=0$ with $a_i\in\mathcal N_0$ forces all $a_i=0$; for $a\in\mathfrak m_A$ and $0\neq b\in A$ one has $b\mid a^n$ for some $n$; every $g\in\mathcal N_0$ differs from the image of some element of $C$ by a non-unit; every element of $A$ is congruent modulo $\mathfrak m_A$ to an element of $C$; and $A$ is the only valuation subring of $L$ containing $C$ in which $\varpi$ is a non-unit. Let $W$ be a complete discrete valuation domain with irreducible $\pi$, let $\sigma:W\to\widehat{\mathcal N_0}$ (adic completion at $\mathfrak m_{\mathcal N_0}$) send $\pi$ to the image of $\varpi$, let $E\ge 1$ and let $\iota:\widehat{\mathcal N_0}\xrightarrow{\sim}W[[X_0,X_1]]/(X_0X_1-\pi^E)$ be a ring isomorphism carrying $\sigma(o)$ to `const` $o$ for all $o\in W$. Finally let $R_1,R_2$ be valuation subrings of $F$ containing $\mathcal N_0$ in which the image of $\varpi$ is a non-unit, and let $x,y\in\mathcal N_0$ have $\iota$-images $\gamma_U\cdot$`U`$(\pi^E)$ and $\gamma_V\cdot$`V`$(\pi^E)$ for units $\gamma_U,\gamma_V$ of the crossing model, with $x$ a unit of $R_1$ and a non-unit of $R_2$, and $y$ a non-unit of $R_1$ and a unit of $R_2$. Then every $f\in F$ lying in $R_1$, in $R_2$ and in $\mathcal O_P$ for all $P\in S$ is integral over $\mathcal N_0$, and satisfies $P.\mathrm{evalAt}(f)\in A$ for every $P\in S$.
--
--   This is the algebraic form of the maximum principle on a closed annulus: a function integral at both ends of a node and at all places centred at the node is integral over the node ring, and therefore takes values in the valuation ring $A$ of constants. It is applied to the node annuli of the supersingular model of the relevant modular curve in [`ModularCurve.FullLevel.evalAt_mem_of_mem_integers_igusaEnd_of_forall_mem_nodePlaces`](thm.html#ModularCurve.FullLevel.evalAt_mem_of_mem_integers_igusaEnd_of_forall_mem_nodePlaces) and its variant for primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring.lean

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

theorem AlgebraicCurve.NodeAnnulusEngine.isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring
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

    (hκ : ∀ a : ↥A, ∃ c : ↥C, a - ⟨(c : L), hC c c.2⟩ ∈ maximalIdeal ↥A)
    (huniq : ∀ V : ValuationSubring L, (∀ c : L, c ∈ C → c ∈ V) → ((ϖ : ↥C) : L) ∈ V.nonunits → V = A)

    (R₁ R₂ : ValuationSubring F)
    (h₁ : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₁) (h₂ : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₂)
    (hϖ₁ : algebraMap L F ((ϖ : ↥C) : L) ∈ R₁.nonunits) (hϖ₂ : algebraMap L F ((ϖ : ↥C) : L) ∈ R₂.nonunits)

    (x y : ↥𝒩₀) (γU γV : (UVCrossingModel W (π ^ E))ˣ)
    (hιx : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) x) =
      (γU : UVCrossingModel W (π ^ E)) * U (π ^ E))
    (hιy : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) y) =
      (γV : UVCrossingModel W (π ^ E)) * V (π ^ E))
    (hx₁ : ((x : ↥𝒩₀) : F) ∉ R₁.nonunits) (hx₂ : ((x : ↥𝒩₀) : F) ∈ R₂.nonunits)
    (hy₁ : ((y : ↥𝒩₀) : F) ∈ R₁.nonunits) (hy₂ : ((y : ↥𝒩₀) : F) ∉ R₂.nonunits) :
    ∀ f : F, f ∈ R₁ → f ∈ R₂ → (∀ P ∈ S, f ∈ P.toValuationSubring) →
      IsIntegral ↥𝒩₀ f ∧ ∀ P ∈ S, P.evalAt f ∈ A := by sorry
