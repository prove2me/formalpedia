-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_algEquiv_of_integers_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_algEquiv_of_integers_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/660494c6-17fb-58da-bc9b-f16b13c3518f
-- title:
--   Regular prolongations with equal valuation rings have k-isomorphic residue fields
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, with residue field $k = \mathrm{ResidueField}\,A$, let $F$ be a field equipped with an $L$-algebra structure, and let $\bar F_1, \bar F_2$ be fields equipped with $k$-algebra structures. Suppose given two regular prolongations $R_1 : \mathrm{RegularProlongation}\,A\,F\,\bar F_1$ and $R_2 : \mathrm{RegularProlongation}\,A\,F\,\bar F_2$; thus each $R_i$ consists of a valuation subring $\mathcal O_i \subseteq F$ together with a ring homomorphism $\mathrm{res}_i : \mathcal O_i \to \bar F_i$ such that, for $x \in L$, the image of $x$ in $F$ lies in $\mathcal O_i$ exactly when $x \in A$; $\mathrm{res}_i$ is surjective with kernel the maximal ideal of $\mathcal O_i$; $\mathrm{res}_i$ agrees on the image of $A$ with the composite of the residue map $A \to k$ and the structure map $k \to \bar F_i$; and every nonzero $f \in F$ admits $c \in L$ with $c \cdot f \in \mathcal O_i$ and $\mathrm{res}_i(c \cdot f) \ne 0$. If $\mathcal O_1 = \mathcal O_2$ as valuation subrings of $F$, then the type of $k$-algebra isomorphisms $\bar F_1 \simeq \bar F_2$ is nonempty. The conclusion asserts the existence of such an isomorphism, with no canonical choice recorded.
--
--   This is the uniqueness-up-to-isomorphism statement for the residue field of a prolongation of a valuation of $L$ to an extension field $F$: the residue field is determined, as an algebra over the residue field of $A$, by the valuation subring of $F$ alone. It is used in the treatment of charts on modular curves, in [`ModularCurve.FullLevel.exists_algEquiv_quotField_of_chart_over`](thm.html#ModularCurve.FullLevel.exists_algEquiv_quotField_of_chart_over) and its variants for the cases of residue characteristic dividing the level at $2$ and at $3$, to compare residue fields arising from two different presentations of one and the same valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_algEquiv_of_integers_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_algEquiv_of_integers_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
    [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
    (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
    (heq : R₁.integers = R₂.integers) :
    Nonempty (Fb₁ ≃ₐ[IsLocalRing.ResidueField A] Fb₂) := by sorry
