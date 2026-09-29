-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_taylorRem_add
-- name    : AlgebraicCurve.Place.taylorRem_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/78b1de16-b3bc-5a26-a78e-58948ac73ff2
-- title:
--   Additivity of Taylor remainders at a rational place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F/K$ in the sense of the project, i.e. a valuation subring $\mathcal O_v =$ `v.toValuationSubring` of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Assume $v$ is rational, meaning that the composite $K \to \mathcal O_v \to \mathcal O_v/\mathfrak m_v$ into the residue field is surjective. Let $t \in F$ satisfy $\operatorname{ord}_v t = 1$, where $\operatorname{ord}_v$ is minus the logarithm of the associated height-one-spectrum adic valuation, and let $f, g \in \mathcal O_v$. Write $\rho_r$ for the $r$-th Taylor remainder of a function at $v$ along $t$, defined by $\rho_0(h) = h$ and $\rho_{r+1}(h) = \bigl(\rho_r(h) - \iota(\operatorname{ev}_v(\rho_r(h)))\bigr)t^{-1}$, where $\iota : K \to F$ is the structure map and $\operatorname{ev}_v(h) \in K$ is the element of $K$ representing the residue class of $h$ when $h \in \mathcal O_v$ and $0$ otherwise. Then for every $r \in \mathbb N$ one has $\rho_r(f+g) = \rho_r(f) + \rho_r(g)$.
--
--   This is the additivity half of the statement that, at a rational place with uniformiser $t$, the passage to Taylor remainders (and hence to Taylor coefficients) is a $K$-linear operation on the functions regular at $v$. It is used for the corresponding additivity of the Taylor coefficients, [`AlgebraicCurve.Place.taylorCoeff_add`](thm.html#AlgebraicCurve.Place.taylorCoeff_add), which makes each row of a jet matrix linear in the section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_taylorRem_add.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorRem_add
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (r : ℕ) :
    taylorRem v t (f + g) r = taylorRem v t f r + taylorRem v t g r := by sorry
