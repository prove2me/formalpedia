-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq
-- name    : AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/55fadbf2-8d9e-519d-bf4e-525b671655aa
-- title:
--   Order at a place computed by any valuation with the same ring
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing the image of $K$ under the structure map, distinct from $F$ itself, and a principal ideal ring. Let $w$ be a valuation on $F$ with values in $\mathbb{Z}^{m0} = \mathrm{WithZero}(\mathrm{Multiplicative}\ \mathbb{Z})$ whose valuation subring coincides with the valuation subring of $v$, and suppose there is an element $\pi \in F$ with $w(\pi) = \exp(-1)$, the image of $-1 \in \mathbb{Z}$ in $\mathbb{Z}^{m0}$. Then for every nonzero $f \in F$ one has $v.\mathrm{ord}(f) = -\mathrm{log}(w(f))$, where by definition $v.\mathrm{ord}(f)$ is $-\mathrm{log}$ of the value at $f$ of the adic valuation attached to $v$, namely the height-one-spectrum valuation on $F$ of the corresponding prime of the valuation subring. Thus $w$, normalised so as to take the value $\exp(-1)$ somewhere, computes the order function of the place on the nose, not merely up to equivalence.
--
--   This is the normalisation transfer for the order function of a place: equivalence of valuations determines the conditions $w(x) \le 1$, $=1$, $<1$, but not the integer order, and attaining the value $\exp(-1)$ pins down the normalisation. It is used throughout the treatment of divisors on curves, for instance when identifying the order functions of the places of a rational function field with the valuations given by explicit uniformisers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (w : Valuation F (WithZero (Multiplicative ℤ))) (hw : w.valuationSubring = v.toValuationSubring) {π : F} (hπ : w π = WithZero.exp (-1 : ℤ)) {f : F} (hf : f ≠ 0) : v.ord f = -WithZero.log (w f) := by sorry
