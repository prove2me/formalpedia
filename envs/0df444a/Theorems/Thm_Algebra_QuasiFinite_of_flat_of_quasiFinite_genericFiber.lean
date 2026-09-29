-- Prove2me | Theorems.Thm_Algebra_QuasiFinite_of_flat_of_quasiFinite_genericFiber
-- name    : Algebra.QuasiFinite.of_flat_of_quasiFinite_genericFiber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/622ed15f-c81c-5b09-a03a-c4ac40a3206d
-- title:
--   Quasi-finiteness from flatness and a quasi-finite generic fibre
-- statement:
--   Let $R$ be a commutative Noetherian domain satisfying `Ring.DimensionLEOne`, i.e. every nonzero prime ideal of $R$ is maximal, let $B$ be a commutative ring equipped with an $R$-algebra structure which is flat as an $R$-module and of finite type as an $R$-algebra, and let $K$ be a field with an $R$-algebra structure making it a fraction field of $R$ (`IsFractionRing R K`). The hypothesis is that the generic fibre $K \otimes_R B$ is quasi-finite over $K$ in the sense of `Algebra.QuasiFinite`; by `Algebra.QuasiFinite.iff_finite_primesOver` this amounts to saying that each prime of $K$ has only finitely many primes of $K \otimes_R B$ above it. The conclusion is that $B$ is quasi-finite over $R$ in the same sense, so that every prime ideal of $R$ has only finitely many primes of $B$ lying over it. No separatedness, properness or geometric hypothesis enters; the statement is purely about the ring map $R \to B$.
--
--   This is the affine form of the standard fact that, over a Noetherian domain of dimension at most one, a flat algebra of finite type with quasi-finite generic fibre is quasi-finite everywhere; the special fibres cannot acquire positive-dimensional components. It is used to obtain the scheme-theoretic statement [`AlgebraicGeometry.LocallyQuasiFinite.of_flat_of_locallyQuasiFinite_genericFiber`](thm.html#AlgebraicGeometry.LocallyQuasiFinite.of_flat_of_locallyQuasiFinite_genericFiber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_QuasiFinite_of_flat_of_quasiFinite_genericFiber.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.QuasiFinite.of_flat_of_quasiFinite_genericFiber
    {R B K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.DimensionLEOne R]
    [CommRing B] [Algebra R B] [Module.Flat R B] [Algebra.FiniteType R B]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hgen : Algebra.QuasiFinite K (K ⊗[R] B)) : Algebra.QuasiFinite R B := by sorry
