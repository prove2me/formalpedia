-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
-- name    : AlgebraicCurve.exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/d79b5aa0-413b-5548-bd3c-dc7f5701de40
-- title:
--   Eventual exactness of ℓ(N· D) for the pole divisor of x
-- statement:
--   Let $K$ be an algebraically closed field and let $F$ be a field carrying a $K$-algebra structure. Let $x \in F$ be transcendental over $K$, and assume $F$ is finite-dimensional over the intermediate field $K(x)$ obtained by adjoining $x$. Here a place of $F/K$ is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring; a divisor is a finitely supported integer-valued function on the set of such places, $\operatorname{ord}_v f$ is minus the logarithm of the value of $f$ under the adic valuation attached to $v$, and $\deg$ is the additive map sending a divisor to the sum of its coefficients weighted by the local degrees. Let $D$ be a divisor with $D(v) = \max(0, -\operatorname{ord}_v x)$ for every place $v$, i.e. the pole divisor of $x$. Write $\ell(E)$ for the $K$-dimension of the Riemann–Roch space of $E$ and $g = \operatorname{genusFF}(K,F)$ for the $K$-dimension of $H^1(0)$. The conclusion is twofold: $\ell(0) = 1$; and there exists a natural number $M \ge 1$ such that for every $N \ge M$ one has the equality of integers $\ell(N \cdot D) = N \deg D + 1 - g$.
--
--   This is the exact form of the Riemann–Roch theorem (vanishing index of specialty) for large multiples of the pole divisor of a chosen transcendental element, together with the computation of $\ell(0)$ over an algebraically closed base field. It is the input used by the later statements on regular prolongations, where dimensions of Riemann–Roch spaces of multiples of a fixed effective divisor must be known exactly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ell (0 : Divisor K F) = 1 ∧
    ∃ M : ℕ, 1 ≤ M ∧ ∀ N, M ≤ N →
      (ell (N • D) : ℤ) = N * Divisor.degree D + 1 - genusFF K F := by sorry
