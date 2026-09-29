-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits
-- name    : AlgebraicCurve.NodeAnnulusEngine.exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/21a66405-88e2-55d1-85c8-7220585f939f
-- title:
--   Proper valuation rings over mathcal N₀ with varpi invertible come from S
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, and $F$ an $L$-algebra which is a field, essentially of finite type over $L$ and a curve over $L$ in the sense of `IsCurveOver` (every non-zero function has a degree-zero principal divisor, every place has residue field finite over $L$, and $\Omega[F/L]$ is free of rank one over $F$); here a place of $F/L$ is a valuation subring of $F$ containing the image of $L$, different from $F$, and a principal ideal ring. Let $S$ be a set of places, $\mathcal N_0 \subseteq F$ a local subring, and assume $S$ consists exactly of those places $P$ such that $\mathcal N_0$ is contained in the valuation subring of $P$ and, for every non-unit $f$ of $\mathcal N_0$, the value $P.\mathrm{evalAt}(f) \in L$ — the image in $L$ of the residue of $f$ under the inverse of $L \to$ residue field of $P$ — lies in $A$ and in its maximal ideal. Let $C \subseteq L$ be a subring with $C \subseteq A$ whose image under $L \to F$ lies in $\mathcal N_0$, and $\varpi \in C$ an element such that an element $d$ of $C$ has residue $0$ in $A$ exactly when $d \in \varpi C$; assume $C$ is a domain and a discrete valuation ring, every element of $A$ is algebraic over $C$, $A$ is the only valuation subring of $L$ containing $C$ in which $\varpi$ is a non-unit, and the image of $\varpi$ in $\mathcal N_0$ is a non-unit. Then for every valuation subring $O$ of $F$ with $O \neq F$ containing $\mathcal N_0$ and such that the image of $\varpi$ in $F$ does not lie in the maximal ideal of $O$, there exists $P \in S$ whose valuation subring is $O$.
--
--   This identifies the valuation rings of the function field lying over the local ring $\mathcal N_0$ of a node, in which the uniformiser $\varpi$ of the ring of constants stays invertible, as exactly the valuation rings of the places centred at the closed point of $\mathcal N_0$; geometrically, such valuations are closed points of the generic fibre in the open annulus attached to the node. It is used in the integrality statement [`AlgebraicCurve.NodeAnnulusEngine.isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring`](thm.html#AlgebraicCurve.NodeAnnulusEngine.isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring), where it rules out the horizontal valuations, and its proof cites the existence of places with prescribed valuation subring together with the existence of a separating transcendental element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.NodeAnnulusEngine.exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (S : Set (Place L F))
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀]
    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)
    (huniq : ∀ V : ValuationSubring L, (∀ c : L, c ∈ C → c ∈ V) → ((ϖ : ↥C) : L) ∈ V.nonunits → V = A)
    (hϖ𝒩 : ¬ IsUnit (⟨algebraMap L F ((ϖ : ↥C) : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀))
    (O : ValuationSubring F) (hO : ∀ f : F, f ∈ 𝒩₀ → f ∈ O)
    (hϖO : algebraMap L F ((ϖ : ↥C) : L) ∉ O.nonunits) (hOtop : O ≠ ⊤) :
    ∃ P ∈ S, P.toValuationSubring = O := by sorry
