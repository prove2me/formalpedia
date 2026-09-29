-- Prove2me | Theorems.Thm_AlgebraicCurve_ConstantReduction_exists_transcendental_residue
-- name    : AlgebraicCurve.ConstantReduction.exists_transcendental_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/45514e40-16ee-5f6d-b6f0-8b12d02d85a3
-- title:
--   Existence of a doubly transcendental element in a constant reduction
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field equipped with an $L$-algebra structure, and $\bar F$ a field equipped with an algebra structure over the residue field $k = \mathrm{ResidueField}\,A$. Let $R$ be a constant reduction of $F$ along $A$ onto $\bar F$, that is: a valuation subring $\mathcal O = R.\mathrm{integers}$ of $F$, a ring homomorphism $\mathrm{res} \colon \mathcal O \to \bar F$, and a map $P \mapsto R.\mathrm{placeMap}\,P$ from places of $F/L$ to places of $\bar F/k$ (a place being a valuation subring containing the image of the base field, different from the whole field, and a principal ideal ring), subject to: $\mathrm{algebraMap}\,x \in \mathcal O \iff x \in A$ for $x \in L$; $\mathrm{res}$ surjective; $\ker \mathrm{res}$ equal to the maximal ideal of $\mathcal O$; compatibility of $\mathrm{res}$ on constants with the residue map of $A$; for every $f \neq 0$ in $F$ some $c \in L$ with $c \cdot f \in \mathcal O$ and $\mathrm{res}(c\cdot f) \neq 0$; preservation of degrees of places; and compatibility of $\mathrm{res}$ with divisors under $\mathrm{Finsupp.mapDomain}$ of $R.\mathrm{placeMap}$. Assume further that $F/L$ has at least one place. Then there exists $f \in \mathcal O$ such that $\mathrm{res}\,f$ is transcendental over $k$ and $f$, viewed in $F$, is transcendental over $L$.
--
--   This is the basic existence statement in Deuring's theory of constant reduction of a function field: a constant reduction transports a place of $F/L$ to a place of $\bar F/k$, and hence produces an element whose residue is a non-constant function downstairs, with the element itself non-constant upstairs. It is used in the project's comparison of divisor class groups under constant reduction, in particular by the results on torsion in $\mathrm{Pic}^0$ and by the refinement giving control of $[F : L(f)]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ConstantReduction_exists_transcendental_residue.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.exists_transcendental_residue
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) [Nonempty (Place L F)] :
    ∃ f : R.integers, Transcendental (IsLocalRing.ResidueField A) (R.residue f) ∧
      Transcendental L (f : F) := by sorry
