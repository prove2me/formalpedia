-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_int_forall_degree_add_one_sub_le_ell
-- name    : AlgebraicCurve.exists_int_forall_degree_add_one_sub_le_ell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/78089c32-a022-54e7-aa35-900e21224d4f
-- title:
--   Riemann's inequality with a uniform constant γ
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, assume the curve axioms `IsCurveOver K F` — namely that every nonzero $f \in F$ admits a divisor whose coefficient at each place $v$ is $v.\mathrm{ord}\, f$ and whose degree is $0$, that each residue field $\kappa(v)$ is a finite $K$-module, and that the module of Kähler differentials $\Omega_{F/K}$ is free of rank one over $F$ — and assume that $F$ is essentially of finite type over $K$. Here a place of $F/K$ is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring; a divisor is a finitely supported function $D$ from the set of places to $\mathbb{Z}$, and $\deg D = \sum_v D(v)\, \deg v$. The assertion is that there exists an integer $\gamma$, depending only on $F/K$, such that for every divisor $D$ one has $\deg D + 1 - \gamma \le \ell(D)$, where $\ell(D)$ is the $K$-dimension (`Module.finrank`) of the Riemann–Roch space $L(D)$ attached to $D$. The single $\gamma$ is uniform in $D$; no separate hypothesis that places exist is imposed.
--
--   This is Riemann's inequality for a one-variable function field over an arbitrary base field, in the form that provides the constant $\gamma$ absorbing the genus and the constant field, and covering the degenerate case in which $F/K$ has no places at all. It is used to produce places with prescribed behaviour, for instance in [`AlgebraicCurve.Place.exists_not_mem_range_and_forall_ne_ord_nonneg`](thm.html#AlgebraicCurve.Place.exists_not_mem_range_and_forall_ne_ord_nonneg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_int_forall_degree_add_one_sub_le_ell.lean

import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v

theorem AlgebraicCurve.exists_int_forall_degree_add_one_sub_le_ell
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by sorry
