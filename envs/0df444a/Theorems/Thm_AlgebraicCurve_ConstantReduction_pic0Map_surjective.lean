-- Prove2me | Theorems.Thm_AlgebraicCurve_ConstantReduction_pic0Map_surjective
-- name    : AlgebraicCurve.ConstantReduction.pic0Map_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/949c269b-443f-536d-90ef-c0cc6b1095d1
-- title:
--   Surjectivity of the reduction map on Pic⁰
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field equipped with an $L$-algebra structure, and $\bar F$ a field equipped with an algebra structure over the residue field of $A$. Let $R$ be a constant reduction datum of $A$ in $F$ with residue field $\bar F$: that is, a valuation subring $\mathcal{O} \subseteq F$ together with a surjective ring homomorphism $\mathcal{O} \to \bar F$ whose kernel is the maximal ideal of $\mathcal{O}$, whose restriction along $L \to F$ realises $A$ as the preimage of $\mathcal{O}$ and induces the given map on residue fields, such that every nonzero $f \in F$ becomes, after scaling by a constant $c \in L$, an element of $\mathcal{O}$ with nonzero residue; together with a map $P \mapsto \bar P$ from places of $F/L$ to places of $\bar F/\mathrm{Res}(A)$ (places being nontrivial valuation subrings containing the constants and with principal ideals) preserving residue degrees and carrying the divisor of any $f \in \mathcal{O}$ with nonzero residue to the divisor of its residue. Assume moreover that every nonzero element of $F$ has a divisor of degree zero, recorded by the hypothesis `HasPrincipalDivisors L F`. Then the induced homomorphism $\mathrm{Pic}^0(F/L) \to \mathrm{Pic}^0(\bar F/\mathrm{Res}(A))$, obtained from pushforward of divisors along $P \mapsto \bar P$ on degree-zero divisors modulo principal divisors, is surjective.
--
--   This is the divisor-class-group half of Deuring's theory of constant reduction of function fields: reduction of places is onto, and hence so is reduction on degree-zero divisor classes. It is used in the construction of a suitable torsion class on the reduction of a modular curve, via [`ModularCurve.exists_nsmul_eq_pic0_modularFunctionFieldC_residueField`](thm.html#ModularCurve.exists_nsmul_eq_pic0_modularFunctionFieldC_residueField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ConstantReduction_pic0Map_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.pic0Map_surjective
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) [HasPrincipalDivisors L F] :
    Function.Surjective R.pic0Map := by sorry
