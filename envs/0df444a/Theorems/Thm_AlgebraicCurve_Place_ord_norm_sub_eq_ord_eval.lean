-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_norm_sub_eq_ord_eval
-- name    : AlgebraicCurve.Place.ord_norm_sub_eq_ord_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e4bc750c-a34a-535b-9759-09d9e061b7db
-- title:
--   Order of a norm equals order of the polynomial value
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ a $K$-algebra and $F'$ an $F$-algebra which is finite as an $F$-module. Let $v$ be a place of $F$ over $K$ in the sense of the project, i.e. a valuation subring $\mathcal{O}_v = v.\mathrm{toValuationSubring}$ of $F$ containing the image of $K$ under the structure map, different from all of $F$, and a principal ideal ring; write $\operatorname{ord}_v$ for the associated integer-valued invariant, defined as minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation of $F$ attached to the height-one prime of $\mathcal{O}_v$. Let $Q$ be a polynomial with coefficients in $\mathcal{O}_v$, let $x \in F'$, and assume that the image of $Q$ under the coefficientwise map $\mathcal{O}_v \to F$ is the minimal polynomial of $x$ over $F$, and that $\deg(\mathrm{minpoly}_F x) = [F' : F]$. Then for every $b \in \mathcal{O}_v$, $$\operatorname{ord}_v\big(N_{F'/F}(x - b)\big) = \operatorname{ord}_v\big(Q(b)\big),$$ where $b$ is viewed in $F'$ through $F$ on the left, and on the right $Q(b) \in \mathcal{O}_v$ is viewed in $F$.
--
--   This is the standard computation identifying the norm of $x - b$ with the value at $b$ of a minimal polynomial of $x$ with $v$-integral coefficients, up to sign, which the order function ignores. It supplies the integrality-and-order hypothesis used when producing places of $F'$ above a place of $F$ from a simple root of the reduced polynomial, and is invoked in the level-one and level-$N$ cases of place specialisation on modular curves as well as in a divisor-theoretic trace computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_norm_sub_eq_ord_eval.lean

import Mathlib.RingTheory.Norm.Transitivity
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_norm_sub_eq_ord_eval {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra F F'] [Module.Finite F F'] (v : Place K F) (Q : Polynomial v.toValuationSubring) {x : F'} (hQ : Q.map (algebraMap v.toValuationSubring F) = minpoly F x) (hdeg : (minpoly F x).natDegree = Module.finrank F F') (b : v.toValuationSubring) : v.ord (Algebra.norm F (x - algebraMap F F' (b : F))) = v.ord ((Q.eval b : v.toValuationSubring) : F) := by sorry
