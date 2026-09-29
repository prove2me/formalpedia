-- Prove2me | Theorems.Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType
-- name    : Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/7c9500d7-d91d-549e-a2db-381d241e48d4
-- title:
--   Krull dimension equals transcendence degree for finitely generated domains
-- statement:
--   Let $k$ be a field and let $A$ be a commutative ring which is an integral domain and a $k$-algebra of finite type, i.e. $A$ is generated as a $k$-algebra by finitely many elements (the universes of $k$ and of $A$ are unrelated). The conclusion asserts the equality, in `WithBot ℕ∞`, of the Krull dimension `ringKrullDim A` — the supremum of the lengths of strictly increasing chains of prime ideals of $A$, taking values in $\mathbb{N} \cup \{\pm\infty\}$ — and the image in `WithBot ℕ∞` of `Cardinal.toENat (Algebra.trdeg k A)`, where `Algebra.trdeg k A` is the transcendence degree of $A$ over $k$ as a cardinal and `Cardinal.toENat` sends it to $\mathbb{N} \cup \{\infty\}$ (sending infinite cardinals to $\infty$). In particular both sides are the same natural number; the statement thus records at once the finiteness of $\dim A$ and its identification with $\operatorname{trdeg}_k A$.
--
--   This is the fundamental comparison between the combinatorial dimension of an affine variety over a field (chains of prime ideals of its coordinate ring) and the function-theoretic one (the number of algebraically independent elements over $k$). It underlies the dimension theory of schemes of finite type over a field, and is invoked in the project for statements about stalks of integral schemes, their residue fields and the topological Krull dimension of closures of points, and in the production of valuation subrings of function fields from one-dimensional stalks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ℕ∞) := by sorry
