-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single_complex
-- name    : AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/c2f3d739-ee3f-5121-9afd-3ef4808dd282
-- title:
--   Divisibility of the class of P-Q over ℂ
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure, and assume $F$ is a function field in one variable over $\mathbb{C}$ in the sense that some $x \in F$ is transcendental over $\mathbb{C}$ and $F$ is finite-dimensional over the intermediate field $\mathbb{C}(x)$ obtained by adjoining $x$. Assume further `IsCurveOver ℂ F`: every nonzero $f \in F$ admits a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ and $\deg D = 0$; every place of $F/\mathbb{C}$ has residue field finite over $\mathbb{C}$; and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$. Here a place is a valuation subring of $F$ containing $\mathbb{C}$, distinct from $F$ itself, and a principal ideal ring, $\operatorname{ord}_v$ is the associated normalised valuation (minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation), and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Then for every nonzero natural number $n$ and all places $P, Q$ there exists a nonzero $f \in F$ with $n \mid \operatorname{ord}_v(f) - (\delta_P - \delta_Q)(v)$ in $\mathbb{Z}$ for every place $v$, where $\delta_P - \delta_Q$ is the divisor $P - Q$.
--
--   This is the statement that the class of a degree-zero divisor $P - Q$ is divisible by $n$ in the divisor class group of a complex function field in one variable, i.e. divisibility of $\operatorname{Pic}^0$ of a compact Riemann surface, obtained from the Abel and Jacobi inversion theorems. It is the complex-analytic case of [`AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single`](thm.html#AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single), which cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single_complex.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    (n : ℕ) (hn : n ≠ 0) (P Q : Place ℂ F) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place ℂ F,
      (n : ℤ) ∣ v.ord f - (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor ℂ F) v := by sorry
