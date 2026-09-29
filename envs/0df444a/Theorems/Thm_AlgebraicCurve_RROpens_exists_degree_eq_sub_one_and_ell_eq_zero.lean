-- Prove2me | Theorems.Thm_AlgebraicCurve_RROpens_exists_degree_eq_sub_one_and_ell_eq_zero
-- name    : AlgebraicCurve.RROpens.exists_degree_eq_sub_one_and_ell_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/ff9b7b17-5d72-5cfc-9b0b-11ae43db783c
-- title:
--   A divisor of degree g-1 with no sections
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field extension of $K$ which is a curve over $K$ in the sense of the project's class `IsCurveOver`: every nonzero $f \in F$ has an associated divisor recording its orders $\operatorname{ord}_v f$ at all places and of total degree $0$, each place $v$ (a valuation subring of $F$ containing $K$, proper in $F$ and a principal ideal ring) has residue field finite over $K$, and the module of Kähler differentials $\Omega[F/K]$ is free of rank one over $F$; assume moreover that the set of places of $F/K$ is nonempty. Here a divisor is a finitely supported function from places to $\mathbb{Z}$, its degree is $\sum_v D(v)\,[\,\text{residue field of } v : K\,]$, and $\ell(D)$ denotes the $K$-dimension of the Riemann–Roch space of $D$. Given a divisor $K_c$ and a natural number $g$ such that the Riemann–Roch identity $\ell(D) - \ell(K_c - D) = \deg D + 1 - g$ holds for every divisor $D$, the conclusion is that there exists a divisor $D$ with $\deg D = g - 1$ and $\ell(D) = 0$.
--
--   This is the classical statement that a general divisor class of degree $g-1$ on a curve of genus $g$ has no sections, i.e. the theta divisor $W_{g-1}$ is a proper subvariety of $\operatorname{Pic}^{g-1}$; here it is derived purely from the Riemann–Roch identity taken as a hypothesis, together with the existence of places in general position. It feeds the construction of a nonvanishing theta section with trivial stabiliser used in the relative Picard scheme part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RROpens_exists_degree_eq_sub_one_and_ell_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_degree_eq_sub_one_and_ell_eq_zero
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] [Nonempty (Place K F)] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) :
    ∃ D : Divisor K F, Divisor.degree D = (g : ℤ) - 1 ∧ ell D = 0 := by sorry
