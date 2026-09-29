-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem
-- name    : AlgebraicCurve.Place.exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/f3e35def-a5fb-5950-8ae7-9f010e482405
-- title:
--   Finiteness of poles and prescribed values of a non-constant function
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume `HasPrincipalDivisors K F`: every non-zero $f \in F$ admits a finitely supported function $D$ from the places of $F/K$ to $\mathbb{Z}$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ and with $\deg D = 0$. Here a place of $F/K$ is a valuation subring of $F$ that contains $\operatorname{algebraMap}_{K \to F}(a)$ for every $a \in K$, is not all of $F$, and is a principal ideal ring; $\operatorname{ord}_v$ denotes $-\log$ of the associated adic valuation of $F$ with values in $\mathbb{Z}^{m0}$. Let $x \in F$ be such that $x \neq \operatorname{algebraMap}_{K \to F}(c)$ for every $c \in K$, i.e. $x$ is not a constant, and let $S$ be a finite subset of $K$. The assertion is that there exists a finite set $T$ of places of $F/K$ such that every place $t$ lies in $T$ as soon as either $x$ fails to lie in the valuation subring underlying $t$, or there is some $s \in S$ with $0 < \operatorname{ord}_t(x - \operatorname{algebraMap}_{K \to F}(s))$. Only an inclusion is claimed: $T$ may be larger than the set of such places.
--
--   This is the standard finiteness statement that a non-constant function on a curve has only finitely many poles and, for each of finitely many constants $s$, only finitely many zeros of $x - s$; the finite set $T$ plays the role of a "bad set" of places to be avoided. It is used in the specialization argument on the modular curves occurring in the Frey-curve reduction, with $x$ a modular invariant and $S$ a finite set of values to be avoided.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (x : F) (hx : ∀ c : K, x ≠ algebraMap K F c) (S : Finset K) :
    ∃ T : Finset (Place K F), ∀ t : Place K F,
      (x ∉ t.toValuationSubring ∨ ∃ s ∈ S, 0 < t.ord (x - algebraMap K F s)) → t ∈ T := by sorry
