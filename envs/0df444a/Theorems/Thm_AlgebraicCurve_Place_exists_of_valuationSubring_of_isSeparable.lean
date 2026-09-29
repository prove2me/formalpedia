-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_isSeparable
-- name    : AlgebraicCurve.Place.exists_of_valuationSubring_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/f1b88959-3e78-5f9c-8580-6bf9743c30cb
-- title:
--   Proper valuation subrings over K are discrete
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $x \in F$ be such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}` and separable over it. Let $A$ be a valuation subring of $F$ such that $\mathrm{algebraMap}_{K \to F}(a) \in A$ for every $a \in K$, and such that $A \neq \top$, i.e. $A$ is not all of $F$. The assertion is that there exists a place $v$ of $F$ over $K$ in the sense of the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), i.e. a valuation subring of $F$ containing the image of $K$, different from $F$, and whose ring is a principal ideal ring, whose underlying valuation subring `v.toValuationSubring` is exactly $A$. Since the first two defining conditions of a place are hypotheses of the statement and the third follows from them, the mathematical content is that $A$ itself is a principal ideal ring, i.e. that the valuation attached to $A$ is discrete.
--
--   This is the classical statement that every proper valuation ring of a function field in one variable which contains the constant field is a discrete valuation ring, hence a place of the function field, here in a form requiring only that $F$ be finite and separable over some $K(x)$ rather than a hypothesis on the characteristic. It supplies places from valuation subrings for the divisor-theoretic machinery, and is used in establishing integrality of elements lying in all the valuation subrings in question and in producing places at which a chosen element has positive order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_isSeparable.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_of_valuationSubring_of_isSeparable
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤) :
    ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = A := by sorry
