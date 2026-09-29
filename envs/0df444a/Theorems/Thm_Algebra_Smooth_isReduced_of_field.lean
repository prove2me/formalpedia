-- Prove2me | Theorems.Thm_Algebra_Smooth_isReduced_of_field
-- name    : Algebra.Smooth.isReduced_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/9a07b435-41b1-5391-9554-8d3b2dcfee23
-- title:
--   Smooth algebras over a field are reduced
-- statement:
--   Let $K$ be a field and let $R$ be a commutative ring equipped with a $K$-algebra structure (both taken in the base universe), and suppose that $R$ is smooth over $K$ in Mathlib's sense, i.e. `Algebra.Smooth K R`: the algebra $R$ is formally smooth over $K$ and is of finite presentation as a $K$-algebra. The conclusion is that $R$ is a reduced ring: `IsReduced R`, that is, $R$ is nontrivial-free of nilpotents in the sense that every $x \in R$ with $x^n = 0$ for some $n \ge 1$ satisfies $x = 0$, equivalently the nilradical of $R$ vanishes. No further hypotheses are imposed on $R$; in particular no reducedness, regularity or Noetherian assumption is placed on $R$ itself, and the case $R = 0$ is allowed.
--
--   This is the standard fact that a smooth algebra over a field is reduced, here in the finitely presented formally smooth formulation of smoothness. It is used in the analysis of the moduli packages attached to full-level modular curves, where reducedness of various algebras of modular functions and of their base changes is needed, for instance in [`ModularCurve.FullLevel.isReduced_levelModuliPackageAbs_gamma0Pow_of_maximalIdeal_eq_span`](thm.html#ModularCurve.FullLevel.isReduced_levelModuliPackageAbs_gamma0Pow_of_maximalIdeal_eq_span) and in the study of minimal primes of tensor products appearing there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Smooth_isReduced_of_field.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.Smooth.isReduced_of_field
    (K R : Type) [Field K] [CommRing R] [Algebra K R] [Algebra.Smooth K R] :
    IsReduced R := by sorry
