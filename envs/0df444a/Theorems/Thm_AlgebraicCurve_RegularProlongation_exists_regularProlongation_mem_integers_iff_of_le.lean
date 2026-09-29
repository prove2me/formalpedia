-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_regularProlongation_mem_integers_iff_of_le
-- name    : AlgebraicCurve.RegularProlongation.exists_regularProlongation_mem_integers_iff_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/2761ab46-5721-566a-a622-560189974e24
-- title:
--   Coarsening a regular prolongation preserves residual transcendence
-- statement:
--   Let $L$ be a field with valuation subrings $A \le A'$, let $F$ be a field extension of $L$ (in universe $u$), and let $Fb$ be a field that is an algebra over the residue field $\kappa(A)$ of $A$. Let $R$ be a regular prolongation of $A$ to $F$ with residue field $Fb$: that is, a valuation subring $R.\mathrm{integers}$ of $F$ together with a ring homomorphism $R.\mathrm{residue} : R.\mathrm{integers} \to Fb$ which is surjective, has kernel the maximal ideal of $R.\mathrm{integers}$, satisfies $\mathrm{algebraMap}_{L\to F}(x) \in R.\mathrm{integers} \iff x \in A$ for all $x \in L$, is compatible with $A \to \kappa(A) \to Fb$ on elements of $A$, and is such that every nonzero $f \in F$ admits $c \in L$ with $c \cdot f \in R.\mathrm{integers}$ of nonzero residue. Let $f \in F$ lie in $R.\mathrm{integers}$ and have residue transcendental over $\kappa(A)$. Then there exist a field $Fb'$ in universe $u$, an algebra structure on $Fb'$ over the residue field $\kappa(A')$ of $A'$, and a regular prolongation $R'$ of $A'$ to $F$ with residue field $Fb'$, such that $R.\mathrm{integers} \le R'.\mathrm{integers}$, such that for all $x \in F$ one has $x \in R'.\mathrm{integers}$ exactly when $a \cdot x \in R.\mathrm{integers}$ for some $a \in L$ with $A'$-valuation $1$, and such that the $R'$-residue of $f$ is transcendental over $\kappa(A')$.
--
--   This is the passage from a regular prolongation (constant reduction) of a valuation ring $A$ of the constant field to a prolongation of a coarsening $A'$ of $A$, realised as the localisation of $R.\mathrm{integers}$ at the prime determined by $A'$, together with the persistence of residual transcendence. It feeds the analysis of regular prolongations over valuation rings of Krull dimension at most one, being cited by [`AlgebraicCurve.RegularProlongation.exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one`](thm.html#AlgebraicCurve.RegularProlongation.exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_regularProlongation_mem_integers_iff_of_le.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_regularProlongation_mem_integers_iff_of_le.{u}
    {L : Type*} [Field L] (A A' : ValuationSubring L) (hA : A ≤ A')
    {F : Type u} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : RegularProlongation A F Fb)
    (f : F) (hf : f ∈ R.integers)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hf⟩)) :
    ∃ (Fb' : Type u) (_ : Field Fb') (_ : Algebra (IsLocalRing.ResidueField A') Fb')
      (R' : RegularProlongation A' F Fb') (hle : R.integers ≤ R'.integers),
      (∀ x : F, x ∈ R'.integers ↔ ∃ a : L, A'.valuation a = 1 ∧ a • x ∈ R.integers) ∧
      Transcendental (IsLocalRing.ResidueField A') (R'.residue ⟨f, hle hf⟩) := by sorry
