-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_algEquiv_residue_eq_of_integers_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_algEquiv_residue_eq_of_integers_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/e89549ea-0960-5d0e-b629-70807b4dbc53
-- title:
--   Residue-compatible isomorphism of reduced fields for equal prolongations
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring with residue field $\kappa = A/\mathfrak{m}_A$, and $F$ a field extension of $L$. Let $\bar F_1$ and $\bar F_2$ be fields, each equipped with a $\kappa$-algebra structure, and let $R_1$ be a regular prolongation of $A$ to $F$ with reduced field $\bar F_1$ and $R_2$ one with reduced field $\bar F_2$; that is, each $R_i$ consists of a valuation subring $R_i.\mathrm{integers}$ of $F$ together with a ring homomorphism $\rho_i$ from it to $\bar F_i$ such that an element of $L$ lies in $A$ exactly when its image in $F$ lies in $R_i.\mathrm{integers}$, $\rho_i$ is surjective with kernel the maximal ideal of $R_i.\mathrm{integers}$, $\rho_i$ agrees on the image of $A$ with the $\kappa$-algebra structure map composed with reduction $A \to \kappa$, and every nonzero $f \in F$ has an $L$-multiple lying in $R_i.\mathrm{integers}$ with nonzero residue. Assume the two valuation subrings coincide: for every $f \in F$, $f \in R_1.\mathrm{integers}$ if and only if $f \in R_2.\mathrm{integers}$. Then there exists a $\kappa$-algebra isomorphism $\iota : \bar F_1 \to \bar F_2$ with $\iota(\rho_1(f)) = \rho_2(f)$ for every $f$ in the common ring of integers.
--
--   This is the residue-compatible refinement of the uniqueness of the reduced field attached to a prolongation of a valuation ring $A \subseteq L$ to an extension $F$: two regular prolongations with the same ring of integers have canonically isomorphic reduced fields, and the isomorphism transports residues of elements of $F$. It is used in the study of Igusa-type reductions of modular curves, where a reduced place may be presented by different choices of reduced field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_algEquiv_residue_eq_of_integers_eq.lean

import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_algEquiv_residue_eq_of_integers_eq
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField ↥A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField ↥A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (hint : ∀ f : F, f ∈ R₁.integers ↔ f ∈ R₂.integers) :
    ∃ ι : Fbar₁ ≃ₐ[ResidueField ↥A] Fbar₂,
      ∀ (f : F) (h₁ : f ∈ R₁.integers), ι (R₁.residue ⟨f, h₁⟩) = R₂.residue ⟨f, (hint f).mp h₁⟩ := by sorry
