-- Prove2me | Theorems.Thm_AlgebraicCurve_WeilDatum_pairing_ne_zero
-- name    : AlgebraicCurve.WeilDatum.pairing_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/3d128c29-1893-522c-bcd6-5672b2b8bf95
-- title:
--   Non-vanishing of the Weil datum pairing
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $n$ be a natural number, and let $d$ be a Weil datum of order $n$ for $F/K$. Such a datum consists of two divisors $D_1, D_2$, that is, finitely supported integer-valued functions on the set of places of $F/K$ (a place being a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring), together with two nonzero elements $f_1, f_2 \in F$, subject to: $v.\mathrm{ord}(f_i) = n \cdot D_i(v)$ for every place $v$ and $i = 1,2$; pointwise disjointness, namely $D_1(v) = 0$ or $D_2(v) = 0$ for every $v$; and rationality, namely every place $v$ with $D_1(v) \neq 0$ or $D_2(v) \neq 0$ satisfies $v.\mathrm{IsRational}$, i.e. the map $K \to v.\mathrm{ResidueField}$ is surjective. The assertion is that the element of $K$
--   $$d.\mathrm{pairing} = \frac{\mathrm{evalFun}(f_1, D_2)}{\mathrm{evalFun}(f_2, D_1)}, \qquad \mathrm{evalFun}(f, D) = \prod_{v} (v.\mathrm{evalAt}\, f)^{D(v)},$$
--   the products being over the supports of the respective divisors, is nonzero.
--
--   This is the non-degeneracy-free first step in Weil's divisor-theoretic construction of the pairing $e_n$ on $n$-torsion divisor classes: the defining expression $f_1(D_2)/f_2(D_1)$ makes sense as an element of $K^\times$. It is used in the passage from explicit data to a homomorphism on torsion classes, in [`AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing`](thm.html#AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_WeilDatum_pairing_ne_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_WeilDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.WeilDatum.pairing_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d : WeilDatum K F n) : d.pairing ≠ 0 := by sorry
