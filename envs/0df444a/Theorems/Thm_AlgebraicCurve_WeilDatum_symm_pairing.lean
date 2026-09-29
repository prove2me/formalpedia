-- Prove2me | Theorems.Thm_AlgebraicCurve_WeilDatum_symm_pairing
-- name    : AlgebraicCurve.WeilDatum.symm_pairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/6bebe738-7b52-5414-b4de-1d1d129ed6d1
-- title:
--   Antisymmetry of the pairing of a Weil datum
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $n$ be a natural number. Let $d$ be a Weil datum of order $n$ for $F/K$, that is: two divisors $D_1, D_2$ (finitely supported integer-valued functions on the places of $F/K$, a place being a proper valuation subring of $F$ containing the image of $K$ whose valuation ring is a principal ideal ring), two nonzero elements $f_1, f_2$ of $F$ such that $\mathrm{ord}_v(f_i) = n\,D_i(v)$ at every place $v$, the condition that at each place $v$ at least one of $D_1(v)$, $D_2(v)$ vanishes, and the condition that at each place $v$ where $D_1(v) \ne 0$ or $D_2(v) \ne 0$ the map $K \to$ (residue field of $v$) is surjective. Write $f(D) = \prod_{v} (\mathrm{ev}_v f)^{D(v)} \in K$ for the evaluation of $f$ at a divisor, the product being over the support of $D$, and let the pairing of $d$ be $f_1(D_2)/f_2(D_1)$. Let $d.\mathrm{symm}$ be the datum obtained by exchanging $(D_1,f_1)$ with $(D_2,f_2)$. The assertion is the equality in $K$: the pairing of $d.\mathrm{symm}$ equals the inverse of the pairing of $d$.
--
--   This is the antisymmetry (skew-symmetry) of the Weil pairing in its divisor-theoretic form $e_n(D_2,D_1) = e_n(D_1,D_2)^{-1}$, stated at the level of explicit data rather than of divisor classes; the full alternating property $e_n(D,D)=1$ requires in addition a moving lemma, since a Weil datum has divisors with disjoint support. It is used in [`AlgebraicCurve.WeilDatum.pairing_eq_of_isPrincipal_sub`](thm.html#AlgebraicCurve.WeilDatum.pairing_eq_of_isPrincipal_sub) and in [`AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing`](thm.html#AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing), which passes from data to a homomorphism on the $n$-torsion of the degree-zero divisor class group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_WeilDatum_symm_pairing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_WeilDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.WeilDatum.symm_pairing {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d : WeilDatum K F n) : d.symm.pairing = d.pairing⁻¹ := by sorry
