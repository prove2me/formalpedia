-- Prove2me | Theorems.Thm_Complex_exists_trivialization_add_pow
-- name    : Complex.exists_trivialization_add_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/11ff3b9d-4e11-5d66-a39e-7bcdf2e68029
-- title:
--   Trivialising ζ ↦ b + ζ^e away from a ray
-- statement:
--   Let $b \in \mathbb{C}$, let $\theta \in \mathbb{R}$, let $e$ be a nonzero natural number, and let $U \subseteq \mathbb{C}$ be a set with the property that for every $z \in U$ and every real $t \ge 0$ one has $b + t e^{i\theta} \neq z$; that is, $U$ is disjoint from the closed ray issuing from $b$ in the direction $\theta$, the ray $\{b + t e^{i\theta} : t \ge 0\}$, which in particular excludes the point $b$ itself. Then there is a homeomorphism $H$ from the subtype given by the preimage $(\zeta \mapsto b + \zeta^{e})^{-1}(U)$, with its subspace topology from $\mathbb{C}$, onto the product $U \times \mathrm{Fin}\,e$ (the set $U$ with its subspace topology, times a discrete $e$-element set), such that for every $\zeta$ in that preimage the complex number underlying the first component of $H(\zeta)$ is $b + \zeta^{e}$. Thus $H$ is compatible with the two maps to $U$: it trivialises $\zeta \mapsto b + \zeta^{e}$ over $U$ as an $e$-sheeted covering, with the sheets indexed by $\mathrm{Fin}\,e$. No connectivity or openness assumption on $U$ is imposed beyond the avoidance of the ray.
--
--   This is the statement that the $e$-th power map, translated to be centred at $b$, admits a global trivialisation over any region avoiding a closed ray from $b$, the elementary source of single-valued $e$-th roots on a slit plane. It is used in the construction of the scaling data for the dissection of an algebraic curve, via [`AlgebraicCurve.exists_dissectionScaleData`](thm.html#AlgebraicCurve.exists_dissectionScaleData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_trivialization_add_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.exists_trivialization_add_pow {b : ℂ} {θ : ℝ} {e : ℕ} (he : e ≠ 0) {U : Set ℂ}
    (hray : ∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → b + t * Complex.exp (θ * Complex.I) ≠ z) :
    ∃ H : ((fun ζ : ℂ => b + ζ ^ e) ⁻¹' U) ≃ₜ U × Fin e,
      ∀ ζ, ((H ζ).1 : ℂ) = b + (ζ : ℂ) ^ e := by sorry
