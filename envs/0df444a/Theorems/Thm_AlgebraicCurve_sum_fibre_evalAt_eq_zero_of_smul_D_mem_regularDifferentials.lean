-- Prove2me | Theorems.Thm_AlgebraicCurve_sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials
-- name    : AlgebraicCurve.sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/90558a3d-8a5f-58e8-9fe5-e7e192d7424a
-- title:
--   Vanishing of the fibre sum of a regular differential's coefficient
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and let $F$ be a field equipped with a $K$-algebra structure, subject to the hypothesis that there exists $x \in F$ transcendental over $K$ with $F$ finite-dimensional over the intermediate field $K(x)$, and to `IsCurveOver K F`, i.e. every nonzero element of $F$ has a degree-zero principal divisor, every place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$. Here a place $v$ is a valuation subring of $F$ other than $F$ itself which contains the image of $K$ and is a principal ideal ring; $\operatorname{ord}_v$ is the associated normalised integer valuation, and $v.\mathrm{evalAt}\,g \in K$ is the residue of $g$ at $v$ read back through $K \to \kappa(v)$ when $g$ lies in the valuation subring, and $0$ otherwise. Let $f, h \in F$ be such that $h \cdot \mathrm{d}f$ lies in `regularDifferentials K F`, that is, for every place $v$ it equals $c \cdot \mathrm{d}\pi_v$ for some $c$ in the valuation subring of $v$, where $\pi_v$ is the chosen uniformiser at $v$. Let $t \in K$ be such that every place $v$ with $\operatorname{ord}_v(f - t) > 0$ has $\operatorname{ord}_v(f - t) = 1$, and let $Z$ be a finite set of places whose members are exactly the places with $\operatorname{ord}_v(f - t) > 0$. Then $\sum_{v \in Z} v.\mathrm{evalAt}\,h = 0$.
--
--   This is the statement that the trace to $\mathbb{P}^1$ of a regular differential is regular, hence zero: summing the coefficient $h$ of $\omega = h\,\mathrm{d}f$ over an unramified fibre of $f$ above a point $t \in K$ gives $0$. It is used in the analytic part of the construction of the Abel–Jacobi map, in [`AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials
    (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (f h : F) (hω : h • KaehlerDifferential.D K F f ∈ regularDifferentials K F)
    (t : K)
    (hsimple : ∀ v : Place K F,
      0 < v.ord (f - algebraMap K F t) → v.ord (f - algebraMap K F t) = 1)
    (Z : Finset (Place K F)) (hZ : ∀ v : Place K F, v ∈ Z ↔ 0 < v.ord (f - algebraMap K F t)) :
    ∑ v ∈ Z, v.evalAt h = 0 := by sorry
