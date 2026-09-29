-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv
-- name    : AlgebraicCurve.RegularProlongation.exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/a1e8cb09-517c-5843-9e58-6125aff7fe8b
-- title:
--   Transport of a regular prolongation along an L-automorphism
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field that is an $L$-algebra, and $\bar F$ a field that is an algebra over the residue field of $A$. Let $R$ be a regular prolongation of $A$ to $F$ with residue field $\bar F$, that is: a valuation subring $R.\mathrm{integers} \subseteq F$, a ring homomorphism $R.\mathrm{residue} : R.\mathrm{integers} \to \bar F$ such that for every $x \in L$ one has $\mathrm{algebraMap}\,x \in R.\mathrm{integers}$ if and only if $x \in A$, such that $R.\mathrm{residue}$ is surjective with kernel the maximal ideal of $R.\mathrm{integers}$, such that for $a \in A$ the residue of $\mathrm{algebraMap}\,a$ is the image of the residue of $a$ under $\mathrm{ResidueField}(A) \to \bar F$, and such that every $f \in F$ with $f \neq 0$ admits $c \in L$ with $c \cdot f \in R.\mathrm{integers}$ and $R.\mathrm{residue}(c \cdot f) \neq 0$. Let $\theta$ be an $L$-algebra automorphism of $F$. Then there exists a regular prolongation $R'$ of $A$ to $F$ with residue field $\bar F$, together with a proof that for all $f \in F$ one has $f \in R'.\mathrm{integers}$ if and only if $\theta f \in R.\mathrm{integers}$, such that for every $f \in R'.\mathrm{integers}$ the $R'$-residue of $f$ equals the $R$-residue of $\theta f$.
--
--   This is the transport of a regular prolongation of a valuation subring of the constant field along an automorphism of $F$ fixing the constants: $R'$ is the pullback $\theta^{-1}(R)$ with residue map $f \mapsto \overline{\theta f}$. It is used in the construction of the prolongation datum attached to a modular curve at a prime of semistable reduction, where one Gauss prolongation is obtained from another by transporting along an Atkin–Lehner automorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (θ : F ≃ₐ[L] F) :
    ∃ R' : RegularProlongation A F Fbar,
      ∃ hmem : ∀ f : F, f ∈ R'.integers ↔ θ f ∈ R.integers,
        ∀ (f : F) (h : f ∈ R'.integers), R'.residue ⟨f, h⟩ = R.residue ⟨θ f, (hmem f).mp h⟩ := by sorry
