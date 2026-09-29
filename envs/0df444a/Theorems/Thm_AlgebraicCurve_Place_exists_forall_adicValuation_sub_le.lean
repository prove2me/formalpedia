-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_forall_adicValuation_sub_le
-- name    : AlgebraicCurve.Place.exists_forall_adicValuation_sub_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/d6062ae4-7c76-5bed-b9a9-41916e394eab
-- title:
--   Weak approximation at finitely many places of F/K
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra. A place of $F$ over $K$ is, in this development, a valuation subring $\mathcal{O}_v$ of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring; such a $v$ has a height-one prime given by the maximal ideal of $\mathcal{O}_v$, and `adicValuation` is the associated valuation $F \to \mathbb{Z}^{m0} = \mathbb{Z} \cup \{0\}$ written multiplicatively, with $\operatorname{ord}_v$ the corresponding additive order function. Given a finite set $T$ of places of $F$ over $K$, an arbitrary family of target values $\beta$ assigning an element $\beta_v \in F$ to each place, and an arbitrary family of integers $n$ indexed by the places, the assertion is that there exists a single $f \in F$ such that for every $v \in T$ one has $v.\mathrm{adicValuation}(f - \beta_v) \le \exp(n_v)$; equivalently, for each $v \in T$ either $f = \beta_v$ or $\operatorname{ord}_v(f - \beta_v) \ge -n_v$. Only the values of $\beta$ and $n$ at the places in $T$ are constrained; no separability, finiteness or non-degeneracy hypothesis on $F/K$ is imposed, and $T$ may be empty.
--
--   This is the weak approximation (independence of valuations) theorem of Artin–Whaples for the places of $F$ over $K$, in the inequality form: prescribed values can be approximated simultaneously to prescribed precision at finitely many places. It is used to obtain the sharper version with exact prescribed orders, [`AlgebraicCurve.Place.exists_forall_adicValuation_sub_eq`](thm.html#AlgebraicCurve.Place.exists_forall_adicValuation_sub_eq), and in the construction of [`ModularCurve.SSHeckeV2.liftFun_spec`](thm.html#ModularCurve.SSHeckeV2.liftFun_spec).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_forall_adicValuation_sub_le.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.exists_forall_adicValuation_sub_le {K F : Type*} [Field K] [Field F] [Algebra K F]
    (T : Finset (AlgebraicCurve.Place K F)) (β : AlgebraicCurve.Place K F → F)
    (n : AlgebraicCurve.Place K F → ℤ) :
    ∃ f : F, ∀ v ∈ T, v.adicValuation (f - β v) ≤ WithZero.exp (n v) := by sorry
