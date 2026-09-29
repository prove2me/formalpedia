-- Prove2me | Theorems.Thm_Algebra_norm_algebraMap_sub_eq_minpoly_eval
-- name    : Algebra.norm_algebraMap_sub_eq_minpoly_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/f9611323-bf04-5ca3-b036-25de29856356
-- title:
--   Norm of c-x as minimal polynomial value
-- statement:
--   Let $F$ and $F'$ be fields with $F'$ an $F$-algebra that is finite as an $F$-module, let $x \in F'$, and suppose the minimal polynomial of $x$ over $F$ has degree equal to $\operatorname{finrank}_F F' = [F':F]$ (equivalently, $F' = F(x)$). Then for every $c \in F$ the field norm of the element $\iota(c) - x$, where $\iota \colon F \to F'$ is the structure map of the algebra, equals the value at $c$ of the minimal polynomial of $x$ over $F$: $$N_{F'/F}\bigl(\iota(c) - x\bigr) = (\mathrm{minpoly}_F x)(c).$$ The formula is thus in the sign-free shape: no factor $(-1)^{[F':F]}$ appears, this being absorbed by taking $\iota(c) - x$ rather than $x - \iota(c)$. The degree hypothesis cannot be dropped: for $x$ in the image of $F$ and $[F':F] > 1$ the left-hand side is an $[F':F]$-th power while the minimal polynomial is linear.
--
--   This is the classical expression of the characteristic polynomial of a generator of a finite simple field extension as its minimal polynomial, specialised to the norm of a linear translate. It is used in the computation of valuations of norms of elements $x - b$ at a place, via the corollary [`Algebra.norm_algebraMap_sub_eq_eval_minpoly_pow`](thm.html#Algebra.norm_algebraMap_sub_eq_eval_minpoly_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_norm_algebraMap_sub_eq_minpoly_eval.lean

import Mathlib.RingTheory.Norm.Transitivity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.norm_algebraMap_sub_eq_minpoly_eval {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [Module.Finite F F'] (x : F') (hdeg : (minpoly F x).natDegree = Module.finrank F F') (c : F) : Algebra.norm F (algebraMap F F' c - x) = (minpoly F x).eval c := by sorry
