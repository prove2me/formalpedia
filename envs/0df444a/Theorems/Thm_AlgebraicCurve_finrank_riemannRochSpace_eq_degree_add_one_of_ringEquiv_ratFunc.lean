-- Prove2me | Theorems.Thm_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc
-- name    : AlgebraicCurve.finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/169e2c62-3eca-5a49-aa09-af3bde8be727
-- title:
--   Genus-zero Riemann–Roch for effective divisors
-- statement:
--   Let $k$ be an algebraically closed field and let $F$ be a field equipped with a $k$-algebra structure. Assume given a ring isomorphism $e : k(X) \to F$ from the rational function field over $k$, where $k(X)$ is `RatFunc k`, such that $e$ is compatible with the structure maps from $k$, i.e. $e(\iota(c)) = \iota(c)$ for every $c \in k$. Here a place of $F$ over $k$ (the project notion `Place k F`) is a valuation subring of $F$ which contains the image of $k$, is distinct from $F$ itself, and is a principal ideal ring; a divisor is a finitely supported function $E$ from places of $F$ over $k$ to $\mathbb{Z}$, its degree is $\sum_v E(v)\,\deg(v)$, and the Riemann–Roch space of $E$ is the $k$-submodule $\{f \in F \mid v(f) \le \exp(E(v)) \text{ for all places } v\}$ of $F$, where $v$ denotes the $\mathbb{Z}^{m0}$-valued adic valuation attached to the place $v$ and $\exp$ is the canonical embedding of $\mathbb{Z}$ into $\mathbb{Z}^{m0}$. Then for every divisor $E$ with $0 \le E$ pointwise, the $k$-dimension of this Riemann–Roch space, viewed as an integer, equals $\deg E + 1$. Since the right-hand side is positive, the equality in particular asserts finite-dimensionality over $k$.
--
--   This is the Riemann–Roch theorem in genus $0$ for effective divisors, $\ell(E) = \deg E + 1$, transported from $\mathbb{P}^1$ along a $k$-isomorphism $k(X) \cong F$, so that it applies to any function field presented abstractly rather than as $k(X)$ itself. It is used in the construction of functions with prescribed residues at places of the $j$-line, in the lemmas [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_residue_eq_of_regular_of_nonneg`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_residue_eq_of_regular_of_nonneg) and [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_residue_eq_forall_inertia_smul_eq_of_regular_of_nonneg`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_residue_eq_forall_inertia_smul_eq_of_regular_of_nonneg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) (hE : 0 ≤ E) :
    (Module.finrank k (riemannRochSpace E) : ℤ) = E.degree + 1 := by sorry
