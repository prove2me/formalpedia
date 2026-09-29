-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_forall_adicValuation_sub_eq
-- name    : AlgebraicCurve.Place.exists_forall_adicValuation_sub_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/1a0d6aea-4b16-5f53-a8c0-809317dd835c
-- title:
--   Weak approximation with prescribed exact error valuations
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra. A place of $F$ over $K$, in the sense used here, is a valuation subring of $F$ that contains $\mathrm{algebraMap}\,K\,F$ of every element of $K$, is not all of $F$, and is a principal ideal ring; such a ring is a discrete valuation ring, and `adicValuation` is the associated $\mathbb{Z}^{m0}$-valued valuation on $F$ attached to its maximal ideal viewed as a height-one prime. Given a finite set $T$ of such places, an arbitrary family of target elements $\beta_v \in F$ indexed by all places, and an arbitrary family of integers $n_v$ indexed by all places, the theorem asserts the existence of a single $f \in F$ such that for every $v \in T$ one has $v.\mathrm{adicValuation}(f - \beta_v) = \mathrm{WithZero.exp}(n_v)$, where $\mathrm{WithZero.exp}$ is the embedding of $\mathbb{Z}$ into the nonzero part of $\mathbb{Z}^{m0}$. In particular $f - \beta_v \neq 0$ and the normalised order of $f - \beta_v$ at $v$ equals $-n_v$ exactly, simultaneously for all $v \in T$. No hypothesis is imposed on the extension $F/K$ and $T$ may be empty.
--
--   This is the weak approximation (Artin–Whaples) theorem in its sharp form, where both the approximating values and the exact orders of the errors are prescribed at finitely many places at once. It strengthens the inequality form [`AlgebraicCurve.Place.exists_forall_adicValuation_sub_le`](thm.html#AlgebraicCurve.Place.exists_forall_adicValuation_sub_le) and is used in the construction of functions with prescribed local behaviour, via [`AlgebraicCurve.Place.exists_forall_mem_hasValue`](thm.html#AlgebraicCurve.Place.exists_forall_mem_hasValue) and [`AlgebraicCurve.exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt`](thm.html#AlgebraicCurve.exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_forall_adicValuation_sub_eq.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.exists_forall_adicValuation_sub_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (T : Finset (AlgebraicCurve.Place K F)) (β : AlgebraicCurve.Place K F → F)
    (n : AlgebraicCurve.Place K F → ℤ) :
    ∃ f : F, ∀ v ∈ T, v.adicValuation (f - β v) = WithZero.exp (n v) := by sorry
