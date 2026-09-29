-- Prove2me | Theorems.Thm_Complex_locallyIntegrableOn_of_simplePoles
-- name    : Complex.locallyIntegrableOn_of_simplePoles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/8a37fae7-658e-53e7-beac-232165c6ef4a
-- title:
--   Functions with at most simple poles are locally integrable
-- statement:
--   Let $U \subseteq \mathbb{C}$ be a set, assumed open, and let $F, c : \mathbb{C} \to \mathbb{C}$ be arbitrary functions. Suppose that for every $a \in U$ there exists a function $g : \mathbb{C} \to \mathbb{C}$, analytic at $a$ in the sense of `AnalyticAt ℂ g a`, such that the identity $F(z) = c(a)/(z-a) + g(z)$ holds for all $z$ in some punctured neighbourhood of $a$, i.e. eventually in the filter $\mathcal{N}[\neq] a$ of deleted neighbourhoods. The conclusion is `LocallyIntegrableOn F U`: for every $a \in U$ there is a set $V$ belonging to the neighbourhood filter of $a$ relative to $U$ such that $F$ is integrable on $V$ with respect to planar Lebesgue measure on $\mathbb{C}$. No hypothesis is imposed on the values of $F$ or $c$ outside the punctured neighbourhoods, on measurability of $F$ globally, or on the function $c$ beyond the pointwise appearance of $c(a)$ as the residue at $a$.
--
--   This is the standard local integrability input for integral formulae and unfolding computations involving functions with at most simple poles: the planar area integral of $|z|^{-1}$ over a disc converges. It is used in the evaluation of a sum of residues weighted by stabiliser orders at level one, [`UpperHalfPlane.levelOne_sum_residue_div_card_stabilizer_eq_zero`](thm.html#UpperHalfPlane.levelOne_sum_residue_div_card_stabilizer_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_locallyIntegrableOn_of_simplePoles.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex MeasureTheory
open scoped Topology

theorem Complex.locallyIntegrableOn_of_simplePoles
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z) :
    LocallyIntegrableOn F U := by sorry
