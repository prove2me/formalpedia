-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_exists_valuationSubring_mem_iff_of_valuation_lt
-- name    : AlgebraicCurve.Annulus.exists_valuationSubring_mem_iff_of_valuation_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/6e49c087-2b18-5392-a748-ce360ae3d4ce
-- title:
--   Valuation ring of an interior circle of an annulus
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$. Let $\mathrm{An}$ be an annulus datum for $F$ over $A$: a set $\mathrm{An.dom}$ of places of $F/L$ (a place being a valuation subring of $F$ containing the image of $L$, proper, and a principal ideal ring), a parameter $\mathrm{An.param} \in F$ and a modulus $\mathrm{An.modulus}$ in the maximal ideal of $A$, subject to the annulus axioms: each $P \in \mathrm{An.dom}$ is rational (the structure map $L \to$ residue field of $P$ is surjective, so that $P.\mathrm{evalAt}$ evaluates integral elements in $L$), has $\mathrm{An.param}$ integral with value $z(P) := P.\mathrm{evalAt}\,\mathrm{An.param}$ a nonzero element of the maximal ideal of $A$ dividing the modulus by a further element of that ideal; conversely each admissible value is attained by exactly one $P \in \mathrm{An.dom}$; $P.\mathrm{ord}(\mathrm{An.param} - z(P)) = 1$; and the unit principle for functions without zeros or poles on $\mathrm{An.dom}$. Assume every nonzero $f \in F$ has $P.\mathrm{ord}\,f \neq 0$ for only finitely many $P \in \mathrm{An.dom}$, let $c \in L$ satisfy $A.\mathrm{valuation}(\mathrm{An.modulus}) < A.\mathrm{valuation}(c) < 1$, and let the residue field $k$ of $A$ be infinite. Then there is a valuation subring $V$ of $F$ such that, for every $f \in F$, $f \in V$ holds if and only if there is a finite set $t \subseteq k$ with: for all $P \in \mathrm{An.dom}$ such that $c^{-1} z(P) \in A$, if $A.\mathrm{valuation}(z(P)) = A.\mathrm{valuation}(c)$ and the residue of $c^{-1} z(P)$ in $k$ does not lie in $t$, then $f$ lies in the valuation subring of $P$ and $P.\mathrm{evalAt}\,f \in A$; moreover, for $x \in L$, the image of $x$ in $F$ lies in $V$ if and only if $x \in A$.
--
--   This is the Gauss prolongation of $A$ along the interior circle $v(z) = v(c)$ of the annulus, i.e. the valuation of $F$ attached to the generic point of the corresponding component of a semistable reduction, described by a pointwise integrality condition valid off finitely many residue discs (finitely many exceptions are unavoidable, since a function with a pole on the circle may still be Gauss-integral). It is used in the construction of rational-function charts for the components of an annulus, via [`AlgebraicCurve.Annulus.exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt`](thm.html#AlgebraicCurve.Annulus.exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_exists_valuationSubring_mem_iff_of_valuation_lt.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.Annulus.exists_valuationSubring_mem_iff_of_valuation_lt
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hinf : Infinite (IsLocalRing.ResidueField A)) :
    ∃ V : ValuationSubring F,
      (∀ f : F, f ∈ V ↔ ∃ t : Finset (IsLocalRing.ResidueField A), ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
        A.valuation (P.evalAt An.param) = A.valuation c → IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ ∉ t → f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) ∧
      (∀ x : L, algebraMap L F x ∈ V ↔ x ∈ A) := by sorry
