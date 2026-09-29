-- Prove2me | Theorems.Thm_Field_exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable
-- name    : Field.exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/2019d647-332f-56ec-8c30-05aa5d7b7490
-- title:
--   Purely inseparable subextensions when [E:Eᵖ]=p
-- statement:
--   Let $M$ and $E$ be fields with $E$ an $M$-algebra which is finite-dimensional over $M$ and purely inseparable over $M$, let $p$ be a prime, and assume $E$ has characteristic $p$. Suppose moreover that $E$, viewed as a module over the subfield $(\mathrm{frobenius}\ E\ p).\mathrm{fieldRange} = E^p$ consisting of the $p$-th powers in $E$, has $\mathrm{finrank}$ equal to $p$, that is $[E : E^p] = p$. The conclusion is that there exists a natural number $r$ such that the degree $[E : M]$, i.e. `Module.finrank M E`, equals $p^r$, and the image of $M$ in $E$ under `algebraMap M E` coincides, as a subfield of $E$, with the image of the $r$-fold Frobenius $x \mapsto x^{p^r}$, that is with the subfield $E^{p^r}$. Note that the image subfield, not $M$ itself, is what is pinned down: the equality asserted is between `(algebraMap M E).fieldRange` and `(iterateFrobenius E p r).fieldRange`.
--
--   This is the classical description of the finite purely inseparable subextensions of a field $E$ of characteristic $p$ satisfying $[E:E^p]=p$ (as holds for function fields in one variable over a perfect field): they form the chain $E \supseteq E^p \supseteq E^{p^2} \supseteq \cdots$, so that such a subfield is an $r$-fold Frobenius image and the degree is the corresponding power of $p$. Stated purely field-theoretically, it is used in the analysis of maps of curves in characteristic $p$, via [`WeierstrassCurve.Affine.forall_normFormulaAlong_of_isAlgClosed_of_charP_pos`](thm.html#WeierstrassCurve.Affine.forall_normFormulaAlong_of_isAlgClosed_of_charP_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Field_exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Field.exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable
    {M E : Type*} [Field M] [Field E] [Algebra M E] [FiniteDimensional M E]
    [IsPurelyInseparable M E] (p : ℕ) [Fact p.Prime] [CharP E p]
    (hp : Module.finrank (frobenius E p).fieldRange E = p) :
    ∃ r : ℕ, Module.finrank M E = p ^ r ∧
      (algebraMap M E).fieldRange = (iterateFrobenius E p r).fieldRange := by sorry
