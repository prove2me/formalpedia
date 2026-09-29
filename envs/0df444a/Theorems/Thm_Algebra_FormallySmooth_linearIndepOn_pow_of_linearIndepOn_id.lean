-- Prove2me | Theorems.Thm_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id
-- name    : Algebra.FormallySmooth.linearIndepOn_pow_of_linearIndepOn_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/c7ebd99d-7d83-517a-9c49-64981275fa2d
-- title:
--   Formally smooth field extensions are separable in Mac Lane's sense
-- statement:
--   Let $k$ and $K$ be fields in a common universe, with $K$ a $k$-algebra that is formally smooth over $k$ (in Mathlib's sense, `Algebra.FormallySmooth k K`). Let $p$ be a natural number that is prime and suppose $k$ has exponential characteristic $p$; since $p$ is prime this forces $\operatorname{char} k = p$. Let $s$ be a finite subset of $K$ whose underlying set is linearly independent over $k$ for the identity map, i.e. the family $(x)_{x \in s}$ of elements of $s$ itself is $k$-linearly independent. The conclusion is that the family of $p$-th powers indexed by the same set is $k$-linearly independent as well: $(x^p)_{x \in s}$ is linearly independent over $k$, so that any relation $\sum_{x \in s} c_x x^p = 0$ with $c_x \in k$ has all $c_x = 0$ (in particular the $p$-th powers of distinct elements of $s$ are distinct). The statement is the finite-subset form of the assertion that $K$ is separable over $k$ in Mac Lane's sense.
--
--   This is the implication 'formally smooth $\Rightarrow$ separable (in Mac Lane's sense)' for a field extension, the direction complementary to the construction of formally smooth structures from separating transcendence bases; classically it is EGA $0_{\mathrm{IV}}$ 19.6.1. It is used in the proof that an algebra of finite type with a dense set of points whose residue fields are formally smooth is smooth at suitable minimal primes ([`Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField`](thm.html#Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.FormallySmooth.linearIndepOn_pow_of_linearIndepOn_id
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.FormallySmooth k K]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (s : Finset K) (hs : LinearIndepOn k _root_.id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) := by sorry
