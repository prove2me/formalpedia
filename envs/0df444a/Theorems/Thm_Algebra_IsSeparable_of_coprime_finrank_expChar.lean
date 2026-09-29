-- Prove2me | Theorems.Thm_Algebra_IsSeparable_of_coprime_finrank_expChar
-- name    : Algebra.IsSeparable.of_coprime_finrank_expChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/99204e58-d8c7-509a-bc51-83664286672c
-- title:
--   Finite extensions of degree coprime to the exponential characteristic are separable
-- statement:
--   Let $F$ and $E$ be fields with $E$ an $F$-algebra which is finite-dimensional over $F$, and let $q$ be a natural number which is an exponential characteristic of $F$ (so $q = 1$ when $F$ has characteristic zero, and $q = p$ when $F$ has characteristic $p > 0$). Assume that $\operatorname{finrank}_F E$, the $F$-dimension of $E$, is coprime to $q$ in the sense of `Nat.Coprime`, i.e. $\gcd([E:F], q) = 1$. The conclusion is that $E$ is separable over $F$, i.e. `Algebra.IsSeparable F E`: every element of $E$ is separable over $F$. In characteristic zero the hypothesis is vacuous ($q = 1$), so the statement then specialises to the separability of every finite extension; in characteristic $p$ it says that a finite extension whose degree is prime to $p$ is separable.
--
--   This is the standard criterion that the inseparable part of the degree of a finite extension is a power of the exponential characteristic, so that degree coprime to $q$ forces separability. It is used in the project wherever residue or function field extensions of degree prime to the residue characteristic must be recognised as separable, for instance in the unramifiedness computations on integral models of $X_1(N)$ and in the construction of kernel quotients of Weierstrass curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsSeparable_of_coprime_finrank_expChar.lean

import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.IsSeparable.of_coprime_finrank_expChar (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (q : ℕ) [ExpChar F q] (h : Nat.Coprime (Module.finrank F E) q) :
    Algebra.IsSeparable F E := by sorry
