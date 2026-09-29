-- Prove2me | Theorems.Thm_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue
-- name    : AlgebraicCurve.ConstantReduction.linearIndependent_of_linearIndependent_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/4799b2d0-716f-553e-b6bd-c39272f07e14
-- title:
--   Residue linear independence lifts under constant reduction
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, with residue field $k = \mathrm{ResidueField}\,A$; let $F$ be a field that is an $L$-algebra and $\bar F$ a field that is a $k$-algebra. Let $R$ be a constant reduction datum of type `ConstantReduction A F Fbar`: it consists of a valuation subring $\mathcal O = R.\mathrm{integers}$ of $F$, a ring homomorphism $\mathrm{res} \colon \mathcal O \to \bar F$, and a map on places $\mathrm{Place}\,L\,F \to \mathrm{Place}\,k\,\bar F$, subject to: $\mathrm{algebraMap}_{L,F}(x) \in \mathcal O$ exactly when $x \in A$; $\mathrm{res}$ is surjective with kernel the maximal ideal of $\mathcal O$; $\mathrm{res}$ of a constant $a \in A$ is the image of the residue of $a$ under $k \to \bar F$; every nonzero $f \in F$ has an $L$-multiple lying in $\mathcal O$ with nonzero residue; the place map preserves degrees; and for $f \in \mathcal O$ with $\mathrm{res}\,f \neq 0$ the pushforward along the place map of the divisor of $f$ computes the orders of $\mathrm{res}\,f$. Let $v \colon \iota \to \mathcal O$ be a family indexed by an arbitrary type, and suppose the family $i \mapsto \mathrm{res}(v_i)$ in $\bar F$ is linearly independent over $k$. Then the family $i \mapsto (v_i : F)$ is linearly independent over $L$.
--
--   This is the basic independence statement of Deuring's theory of constant reduction of function fields: residue independence over the residue field forces independence over the base field. It is used in the construction of bases adapted to a reduction, and is cited by [`ModularCurve.exists_uniform_adapted_basis`](thm.html#ModularCurve.exists_uniform_adapted_basis).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.linearIndependent_of_linearIndependent_residue
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar)
    {ι : Type*} (v : ι → R.integers)
    (hv : LinearIndependent (IsLocalRing.ResidueField A) (fun i => R.residue (v i))) :
    LinearIndependent L (fun i => (v i : F)) := by sorry
