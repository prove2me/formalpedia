-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_integers_le_of_annulus_attached_of_forall_mem_of_param_mem_units
-- name    : AlgebraicCurve.RegularProlongation.integers_le_of_annulus_attached_of_forall_mem_of_param_mem_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/12b8f238-1b6d-5064-b5de-f6e3b6497d7b
-- title:
--   Uniqueness of the near end of an attached annulus
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring, $F$ a field extension of $L$ and $\bar F$ a field extension of the residue field of $A$. A place of $F/L$ is a proper valuation subring of $F$ containing the image of $L$ whose ideals are principal, $\mathrm{ord}_P$ denotes minus the logarithm of the associated adic valuation on $F$, and $P.\mathrm{evalAt}\,f$ denotes a chosen preimage in $L$ of the residue class of $f$ when $f$ lies in $P$ and $0$ otherwise. Assume: (i) for every $f\neq 0$ in $F$ the set of places $P$ with $\mathrm{ord}_P f\neq 0$ is finite; (ii) $R$ is a regular prolongation of $A$ to $F$ with reduction $\bar F$, i.e. a valuation subring `R.integers` of $F$ together with a surjective ring morphism `R.residue` onto $\bar F$ whose kernel is the maximal ideal, such that $\mathrm{alg}_{L\to F}(x)\in$ `R.integers` iff $x\in A$, the residue map agrees on $A$ with the residue map of $A$ composed with $\kappa_A\to\bar F$, and every $f\neq 0$ has an $L$-multiple in `R.integers` with nonzero residue; (iii) `An` is an annulus for $A$ in $F$, consisting of a set `An.dom` of places, a parameter `An.param`$\in F$ and a modulus in the maximal ideal of $A$, subject to the defining conditions of the structure (rationality of the places of `An.dom`, the parameter lying in each such place with value in the maximal ideal of $A$ dividing the modulus, unique realisability of admissible parameter values by places of `An.dom`, $\mathrm{ord}_P(\mathrm{param}-\mathrm{evalAt}_P\,\mathrm{param})=1$, and the unit principle), summarised here; (iv) $x$ is a place of $\bar F$ over the residue field of $A$, and `An` is attached to $R$ at $x$: `An.param` lies in `R.integers`, $\mathrm{ord}_x$ of its residue equals $1$, and for every $f\in$ `R.integers` with nonzero residue and $\mathrm{ord}_P f=0$ for all $P\in$ `An.dom`, the element $(P.\mathrm{evalAt}\,f)\cdot(P.\mathrm{evalAt}\,\mathrm{param})^{-\mathrm{ord}_x(\bar f)}$ lies in $A$ and is a unit of $A$, for every $P\in$ `An.dom`. Let finally $O$ be a valuation subring of $F$ such that $\mathrm{alg}_{L\to F}(c)\in O$ iff $c\in A$, such that every $f\in F$ lying in every $P\in$ `An.dom` with $P.\mathrm{evalAt}\,f\in A$ belongs to $O$, and such that `An.param` is nonzero with both `An.param` and its inverse in $O$. Then `R.integers` $\le O$.
--
--   The statement expresses the uniqueness of the near end of an annulus attached to a regular prolongation: a valuation subring of $F$ that dominates the sup-norm ring of the annulus and at which the parameter is a unit contains the integers of the prolongation (the Gauss ring of the chart). It is used in the construction of annuli on modular curves, by [`ModularCurve.FullLevel.annulus_separation_of_crossUnits`](thm.html#ModularCurve.FullLevel.annulus_separation_of_crossUnits).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_integers_le_of_annulus_attached_of_forall_mem_of_param_mem_units.lean

import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.integers_le_of_annulus_attached_of_forall_mem_of_param_mem_units
    {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (hfin : ∀ f : F, f ≠ 0 → Set.Finite {P : Place L F | P.ord f ≠ 0})
    (R : RegularProlongation A F Fbar) (An : Annulus A F) (x : Place (ResidueField A) Fbar)
    (hatt : (∃ hz : An.param ∈ R.integers, x.ord (R.residue ⟨An.param, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
        ∀ P ∈ An.dom, ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x.ord (R.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)))
    (O : ValuationSubring F) (hOA : ∀ c : L, algebraMap L F c ∈ O ↔ c ∈ A)
    (hOx : (∀ f : F, (∀ P ∈ An.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O))
    (hz : An.param ∈ O) (hz' : An.param⁻¹ ∈ O) (hz0 : An.param ≠ 0) :
    R.integers ≤ O := by sorry
