-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_support_pushforward_subset
-- name    : AlgebraicCurve.Divisor.support_pushforward_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/b556337c-9535-52f5-a155-26fa2c7e54c5
-- title:
--   Support of a push-forward divisor lies in restricted support
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the three structures forming a scalar tower, and assume $F'$ is integral over $F$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from all of $F$, and a principal ideal ring; a divisor of $F/K$ is a finitely supported function from such places to $\mathbb{Z}$. For a place $w$ of $F'/K$, its restriction $w|_F$ is the valuation subring obtained by pulling back $w$ along $F \to F'$, and its inertia degree is the $\mathbb{F}$-dimension $[\kappa(w) : \kappa(w|_F)]$ of the residue field of $w$ over that of $w|_F$; the push-forward of a divisor $D$ of $F'/K$ is the additive map sending $D$ to $\sum_w [\kappa(w):\kappa(w|_F)]\, D(w)\,\delta_{w|_F}$. The assertion is that, for every divisor $D$ of $F'/K$, the support of the push-forward of $D$ is contained in the image of the support of $D$ under the restriction map $w \mapsto w|_F$.
--
--   This is the elementary bookkeeping statement that the norm (inertia-weighted push-forward) of a divisor along $F \subseteq F'$ is supported on restrictions of places in the support of the original divisor; it permits sums and products indexed by the support of a push-forward to be rewritten as fibrewise sums over the support of $D$. It is used in the evaluation of functions of $F$ against push-forward divisors, in the function-field groundwork for Weil reciprocity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_support_pushforward_subset.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.support_pushforward_subset {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [DecidableEq (Place K F)] (D : Divisor K F') : (Divisor.pushforward F D).support ⊆ D.support.image (fun w => w.restrict F) := by sorry
