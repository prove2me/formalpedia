-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
-- name    : AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/c1ec998a-b18b-5c7a-ab33-5886aab27679
-- title:
--   Proper valuation subrings containing K are places
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $x \in F$ be an element such that $F$ is finite-dimensional over the intermediate field $K(x)$ obtained by adjoining $x$ to $K$ inside $F$. Let $A$ be a valuation subring of $F$ such that the image of every element of $K$ under the structure map $K \to F$ lies in $A$, and such that $A \neq \top$, i.e. $A$ is a proper subring of $F$. The conclusion is that there exists a place $v$ of $F$ over $K$ in the sense of the project's structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22) — that is, a valuation subring of $F$ which contains the image of $K$, is not all of $F$, and is a principal ideal ring — whose underlying valuation subring `v.toValuationSubring` is exactly $A$. Since the first three data of a place are precisely the hypotheses already imposed on $A$, the mathematical content of the assertion is that $A$ is a principal ideal ring, i.e. a discrete valuation ring; no separability, perfectness or characteristic assumption is made.
--
--   This is the characteristic-free statement that every proper valuation ring of a one-variable function field $F/K$ containing the constants is the valuation ring of a place, in the project's sense in which a place is by definition such a ring that is moreover a principal ideal ring. It is the entry point used throughout the divisor-theoretic development, for instance in producing places extending a given valuation or lying over a prescribed place of a subfield.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤) :
    ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = A := by sorry
