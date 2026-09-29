-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_krullDimLE_one_integers
-- name    : AlgebraicCurve.RegularProlongation.krullDimLE_one_integers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/e1b984d5-16ac-5afd-9e49-d96313f1fce5
-- title:
--   Krull dimension at most one passes to a regular prolongation
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring whose ring of elements has Krull dimension at most one (every nonzero prime of $A$ is maximal). Let $F$ be a field equipped with an $L$-algebra structure, and let $\bar F$ be a field equipped with an algebra structure over the residue field $A/\mathfrak m_A$. Let $R$ be a regular prolongation of $A$ to $F$ with residue field $\bar F$, that is: a valuation subring $\mathcal O = R.integers$ of $F$, together with a ring homomorphism $\mathrm{res} \colon \mathcal O \to \bar F$, such that for $x \in L$ one has $x \in A$ if and only if the image of $x$ in $F$ lies in $\mathcal O$; $\mathrm{res}$ is surjective with kernel exactly the maximal ideal of $\mathcal O$; on elements coming from $A$ the map $\mathrm{res}$ agrees with the composite of the residue map of $A$ with $A/\mathfrak m_A \to \bar F$; and for every $f \in F$ with $f \neq 0$ there is $c \in L$ with $c \cdot f \in \mathcal O$ and $\mathrm{res}(c \cdot f) \neq 0$. The conclusion is that $\mathcal O$ again has Krull dimension at most one.
--
--   This records that the regularity clause (no ramification of the prolongation, $e = 1$) forces the prolonged valuation ring to have the same rank bound as the base: a rank-one valuation subring prolongs to a rank-one valuation subring. It is used in the Gauss-ring characterisation of the integers of a prolongation datum, and in the construction of a valuation subring of the function field of the relevant modular curve whose residue data are controlled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_krullDimLE_one_integers.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.krullDimLE_one_integers
    {L : Type*} [Field L] (A : ValuationSubring L) [Ring.KrullDimLE 1 ↥A]
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) :
    Ring.KrullDimLE 1 ↥R.integers := by sorry
