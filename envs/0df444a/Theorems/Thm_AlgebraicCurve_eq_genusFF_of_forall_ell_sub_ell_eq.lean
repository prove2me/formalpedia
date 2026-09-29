-- Prove2me | Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
-- name    : AlgebraicCurve.eq_genusFF_of_forall_ell_sub_ell_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/a0588aa2-2ebe-5c4f-9e7e-baa22303a15f
-- title:
--   Uniqueness of the genus in Riemann–Roch
-- statement:
--   Let $K$ be a perfect field and $F$ a field equipped with a $K$-algebra structure which is essentially of finite type over $K$ and satisfies `IsCurveOver K F`, that is: every nonzero $f \in F$ has a divisor recording its orders $\mathrm{ord}_v(f)$ at all places $v$ of $F/K$ and of degree $0$; every place has residue field finite over $K$; and $\Omega_{F/K}$ is free of rank one over $F$. Assume moreover `ConstantsAreBase K F`, i.e. the Riemann–Roch space $L(0)$ of the zero divisor is exactly the image of $K$ in $F$. Here a divisor is a finitely supported function from places of $F/K$ to $\mathbb{Z}$, its degree is $\sum_v D(v)\,\deg v$, and $\ell(D)$ denotes the $K$-dimension of $L(D)$. Suppose given a divisor $K_c$ and a natural number $g$ such that for every divisor $D$ one has the identity $\ell(D) - \ell(K_c - D) = \deg D + 1 - g$ in $\mathbb{Z}$. Then $g$ equals `genusFF K F`, the $K$-dimension of $H^1$ of the zero divisor, i.e. the adelic genus of $F/K$.
--
--   This is the uniqueness half of the Riemann–Roch theorem: the integer $g$ occurring in any Riemann–Roch pair $(K_c, g)$ for $F/K$ is forced to be the adelic genus $\dim_K H^1(0)$, so no auxiliary choice of canonical divisor can change it. It is used in the construction of constant reductions and curve models, where a Riemann–Roch identity is available for some pair and the genus invariant must be identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.eq_genusFF_of_forall_ell_sub_ell_eq
    {K : Type u} {F : Type v} [Field K] [PerfectField K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F)
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) :
    g = genusFF K F := by sorry
