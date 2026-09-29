-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_mem_iff_smul_mem_of_forall_mem_iff_sections
-- name    : AlgebraicCurve.SemilinearAut.mem_iff_smul_mem_of_forall_mem_iff_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/211b63d4-3208-56fd-94e3-07b4172fd043
-- title:
--   Stability of a section-cut residue disc under a semilinear automorphism
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$. Let $g$ be a semilinear automorphism of $F/L$, i.e. a pair consisting of a ring automorphism of $F$ and a ring automorphism $\mathrm{baseAut}\,g$ of $L$ compatible under the structure map $L \to F$, and assume that $\mathrm{baseAut}\,g$ stabilises $A$, in the sense that $\mathrm{baseAut}\,g(x) \in A \iff x \in A$ for all $x \in L$. Let $S$ be a subring of $F$ and $\chi_0 : S \to$ (residue field of $A$) a ring homomorphism, and assume $f \in S \iff g \cdot f \in S$ for all $f \in F$, and $\chi_0(g \cdot f) = \chi_0(f)$ for all $f \in S$. Let $D$ be a set of places of $F/L$ (a place being a valuation subring of $F$ containing the image of $L$, different from $F$ and a principal ideal ring) such that $P \in D$ holds precisely when: the map $L \to$ (residue field of $P$) is surjective; every $f \in S$ lies in the valuation subring of $P$ and has $P$-value $P.\mathrm{evalAt}(f) \in A$, where $P.\mathrm{evalAt}$ is the residue of $f$ transported back to $L$ along a section of that surjection; and, for every $f \in S$, the $A$-valuation of $P.\mathrm{evalAt}(f)$ is $<1$ exactly when $\chi_0(f) = 0$. Then for every place $P$ of $F/L$, $P \in D$ if and only if $g \cdot P \in D$.
--
--   The set $D$ is a residue disc described through the sections of the stalk $S$ of a model together with its residue character $\chi_0$; the statement says that such a disc is stable, in both directions, under any semilinear automorphism fixing $A$, the stalk and the character. It is used in the construction of semistable coverings of modular curves of full level, where $g$ is an inertia element acting coefficientwise and the disc-stability clause is consumed by the existence statements for level automorphisms moving points into Igusa discs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_mem_iff_smul_mem_of_forall_mem_iff_sections.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.SemilinearAut.mem_iff_smul_mem_of_forall_mem_iff_sections
    {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    (g : SemilinearAut L F)
    (hgA : ∀ x : L, SemilinearAut.baseAut g x ∈ A ↔ x ∈ A)
    (S : Subring F) (χ₀ : ↥S →+* ResidueField ↥A)
    (hS : ∀ f : F, f ∈ S ↔ g • f ∈ S)
    (hχ₀ : ∀ f : ↥S, χ₀ ⟨g • (f : F), (hS (f : F)).mp f.2⟩ = χ₀ f)
    (D : Set (Place L F))
    (hD : ∀ P : Place L F, P ∈ D ↔ P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))
    (P : Place L F) :
    P ∈ D ↔ g • P ∈ D := by sorry
