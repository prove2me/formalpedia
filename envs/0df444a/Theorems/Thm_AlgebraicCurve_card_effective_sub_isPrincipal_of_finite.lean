-- Prove2me | Theorems.Thm_AlgebraicCurve_card_effective_sub_isPrincipal_of_finite
-- name    : AlgebraicCurve.card_effective_sub_isPrincipal_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/5db1a489-975c-50d8-99dd-be51456c6358
-- title:
--   Counting effective divisors in a divisor class over a finite field
-- statement:
--   Let $k$ be a finite field and $F$ a field equipped with a $k$-algebra structure which is a curve over $k$ in the sense of [`AlgebraicCurve.IsCurveOver k F`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ admits a divisor of degree $0$ whose value at each place $v$ is $v.\mathrm{ord}(f)$, each residue field $\kappa(v)$ is a finite-dimensional $k$-module, and the module of Kähler differentials $\Omega[F/k]$ is free of rank one over $F$. Here a place of $F/k$ is a valuation subring of $F$ containing the image of $k$, different from $F$ itself, and a principal ideal ring, and a divisor is a finitely supported function from places to $\mathbb{Z}$, ordered pointwise; a divisor $D$ is principal when there is a nonzero $f \in F$ with $D(v) = v.\mathrm{ord}(f)$ for every place $v$. Assume [`AlgebraicCurve.ConstantsAreBase k F`](def/AlgebraicCurve_AdelicIndex.html#L45), i.e. the Riemann–Roch space of the zero divisor coincides with the image of $k$ in $F$ under the structure map. Then for every divisor $C$, writing $q = \#k$ and $\ell(C) = \dim_k \mathcal{L}(C)$ for the $k$-dimension of the Riemann–Roch space of $C$, one has $(q-1)\cdot N + 1 = q^{\ell(C)}$, where $N$ is the cardinality of the set of divisors $D$ with $D \ge 0$ and $D - C$ principal (the subtraction $q-1$ being truncated subtraction in $\mathbb{N}$).
--
--   This is the standard count of the effective divisors in a given divisor class of a function field over a finite field, equivalently the statement that their number is $\#\mathbb{P}(\mathcal{L}(C)) = (q^{\ell(C)}-1)/(q-1)$. It feeds the construction of the $L$-polynomial of the curve in [`AlgebraicCurve.exists_LPolynomial_of_finite`](thm.html#AlgebraicCurve.exists_LPolynomial_of_finite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_card_effective_sub_isPrincipal_of_finite.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.card_effective_sub_isPrincipal_of_finite
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) (C : AlgebraicCurve.Divisor k F) :
    (Nat.card k - 1) *
        Nat.card {D : AlgebraicCurve.Divisor k F //
          0 ≤ D ∧ AlgebraicCurve.Divisor.IsPrincipal (D - C)} + 1 =
      Nat.card k ^ AlgebraicCurve.ell C := by sorry
