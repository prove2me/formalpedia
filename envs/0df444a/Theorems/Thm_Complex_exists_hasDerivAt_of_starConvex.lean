-- Prove2me | Theorems.Thm_Complex_exists_hasDerivAt_of_starConvex
-- name    : Complex.exists_hasDerivAt_of_starConvex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/620cd8a6-4810-566a-8993-a7ccfbce4fdf
-- title:
--   Primitives of holomorphic functions on star-shaped domains
-- statement:
--   Let $U \subseteq \mathbb{C}$ be an open set, let $q \in U$, and suppose $U$ is star-convex with respect to $q$ over $\mathbb{R}$, i.e. for every $z \in U$ and every $t \in [0,1]$ the point $(1-t)q + tz$ lies in $U$. Let $f : \mathbb{C} \to \mathbb{C}$ be complex differentiable on $U$ (in the sense of `DifferentiableOn ℂ f U`, differentiability within $U$ at each point of $U$). The conclusion asserts the existence of a function $g : \mathbb{C} \to \mathbb{C}$, defined on all of $\mathbb{C}$, such that $g(q) = 0$ and such that for every $z \in U$ the function $g$ has derivative $f(z)$ at $z$ in the strong sense of `HasDerivAt g (f z) z`, that is, differentiability at $z$ with respect to the full neighbourhood filter of $z$ in $\mathbb{C}$, not merely within $U$. Thus $f$ admits a primitive on $U$ normalised to vanish at the centre $q$.
--
--   This is the holomorphic Poincaré lemma for star-shaped domains: a holomorphic function on a star domain is the derivative of a holomorphic function, the star-shaped generalisation of the disc case available in Mathlib. It is used in the construction of primitives on the cells of a dissection of an algebraic curve, in the comparison of path integrals with periods and residues, and in the construction of Eichler integrals of Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_hasDerivAt_of_starConvex.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.exists_hasDerivAt_of_starConvex {U : Set ℂ} (hU : IsOpen U) {q : ℂ} (hq : q ∈ U)
    (hstar : StarConvex ℝ q U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ g : ℂ → ℂ, g q = 0 ∧ ∀ z ∈ U, HasDerivAt g (f z) z := by sorry
