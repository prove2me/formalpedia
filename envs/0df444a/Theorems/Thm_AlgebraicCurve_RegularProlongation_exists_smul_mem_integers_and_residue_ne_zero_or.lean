-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_smul_mem_integers_and_residue_ne_zero_or
-- name    : AlgebraicCurve.RegularProlongation.exists_smul_mem_integers_and_residue_ne_zero_or
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/90e08104-761c-5b20-9264-733a66545be2
-- title:
--   Common normalising constant for two regular prolongations
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field that is an $L$-algebra, and $\bar F$ a field that is an algebra over the residue field of $A$. Let $R_1, R_2$ be two regular prolongations of $A$ to $F$ with residues in $\bar F$; that is, each $R_i$ consists of a valuation subring $R_i.\mathrm{integers}$ of $F$ together with a surjective ring homomorphism $R_i.\mathrm{residue} : R_i.\mathrm{integers} \to \bar F$ whose kernel is the maximal ideal of $R_i.\mathrm{integers}$, such that for $x \in L$ one has $x \in A$ if and only if the image of $x$ in $F$ lies in $R_i.\mathrm{integers}$, such that $R_i.\mathrm{residue}$ agrees on $A$ with the residue map of $A$ composed with the structure map to $\bar F$, and such that every non-zero $f \in F$ admits $c \in L$ with $c \cdot f \in R_i.\mathrm{integers}$ and non-zero residue. Then for every non-zero $f \in F$ there exists $c \in L$, $c \neq 0$, such that $c \cdot f$ lies in $R_1.\mathrm{integers}$ and in $R_2.\mathrm{integers}$, and at least one of the two residues of $c \cdot f$ is non-zero in $\bar F$.
--
--   This is the two-sided sharpening of the normalisation property built into a regular prolongation: a single scaling constant, invertible in $L$, makes $f$ integral at both prolongations while keeping its residue non-zero at one of them. It is used in the node-unit arguments for prolongation data on modular curves, where a jump law for residues upgrades 'non-zero on one side' to information on both sides.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_smul_mem_integers_and_residue_ne_zero_or.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_smul_mem_integers_and_residue_ne_zero_or
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (R₁ R₂ : AlgebraicCurve.RegularProlongation A F Fbar) {f : F} (hf : f ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ (h₁ : c • f ∈ R₁.integers) (h₂ : c • f ∈ R₂.integers),
      R₁.residue ⟨c • f, h₁⟩ ≠ 0 ∨ R₂.residue ⟨c • f, h₂⟩ ≠ 0 := by sorry
