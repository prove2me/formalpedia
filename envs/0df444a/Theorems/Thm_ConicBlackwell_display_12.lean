-- Prove2me | Theorems.Thm_ConicBlackwell_display_12
-- name    : ConicBlackwell.display_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:46:04.576985+00:00
-- url     : https://prove2.me/theorems/60bf4bdd-d731-40f9-b080-a4dbd39b1140
-- title:
--   Display (12) — $\omega_{t+1}v_{t+1}\ge_{\mathcal C^\circ}u_{t+1}-u_t$ (corrected: $u_1$ projected onto $\mathcal C$)
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a nonempty convex compact set, $x_0,x_1\in\mathcal X$, $(\omega_t)$ real weights, $(f_t)$ losses, and $(x_t,u_t)$ the CBA$^+$ run with $u_0=0$. Then for every $t\ge0$
--
--   $$
--   \omega_{t+1}v_{t+1}\ \ge_{\mathcal C^\circ}\ u_{t+1}-u_t,\qquad\text{i.e.}\qquad \omega_{t+1}v_{t+1}-(u_{t+1}-u_t)\in\mathcal C^\circ,\tag{12}
--   $$
--
--   where $v_t=(\langle f_t,x_t\rangle/\kappa,-f_t)$. This is the one-step inequality that, weighted by $\theta_{t+1}/\omega_{t+1}$ and summed, compares the $\theta$-weighted payoffs with the last aggregate payoff.
--
--   Differences from the source:
--   - correction: Algorithm 1 line 4: u₁ = ω₁(⟨f₁, x₁⟩/κ, −f₁) (no projection) → u₀ = 0 and u₁ = π_C(ω₁v₁), the UPDATEPAYOFF rule applied to u₀ = 0; reason: the printed u₁ can leave C, contradicting 'we always have u ∈ C' (p.5): X = [−1, 1], x₁ = 1/10, f₁ = 1, f₂ = −1, ω = 1 gives u₁ = (1/10, −1) ∉ C and x₂ = −10 ∉ X; the two agree whenever ω₁v₁ ∈ C
--   - generalization: t ≥ 1, weights ω_t of the run → every t ∈ ℕ (t = 0 is the step from u₀ = 0 to u₁), any real ω; reason: the identity ω_{t+1}v_{t+1} − u_{t+1} + u_t = π_{C°}(u_t + ω_{t+1}v_{t+1}) uses no sign of ω; t = 0 adds the first step of the corrected run
--   - encoding: ℝⁿ and ℝ × ℝⁿ = ℝⁿ⁺¹ → E n = EuclideanSpace ℝ (Fin n), and lift a x : E (n+1) with the scalar a in coordinate 0; reason: Lean convention of the reused ApproachRegret.ToOLO definitions; same instances (the dimension n = 0 is not excluded; there X ⊆ {0} and the statements stay true)
--   - encoding: κ = max_{x∈X} ‖x‖₂ and v_t = (⟨f_t, x_t⟩/κ, −f_t) → kappa X = sSup of ‖x‖ over X, and payoff X x f = lift (⟪f, x⟫ / kappa X) (−f) with Lean's x/0 = 0; reason: sSup is the max on a nonempty compact X; κ = 0 only when X = {0}, where the page's ⟨f,x⟩/κ is undefined and both coordinates conventions give the same statement
--   - encoding: x ≤_{C°} y → y - x ∈ polar C; reason: the paper's definition of the order, written out
--   - encoding: rounds t ≥ 1 of Algorithm 1 → sequences ℕ → ·, with rounds t ∈ Finset.Icc 1 T; values at index 0 unused (u 0 = 0 is the start of the run); reason: Lean convention; same instances
--   - encoding: π_C(u), the nearest point of C = cone({κ} × X) to u (UPDATEPAYOFF_{CBA+}, p.5) → PerspEpi.projC C u, the unique nearest point if there is one and u otherwise; reason: C is nonempty, closed and convex for nonempty compact convex X (κ > 0: the base {κ} × X is compact and misses 0; κ = 0: X = {0}, C = {0}), so the nearest point exists and is unique and the fallback is never taken
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), proof of Theorem 3.3, display (12), p.9

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_ConicBlackwell_cbaPlusU
import Definitions.Def_ConicBlackwell_cbaPlusX
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **Display (12)**, Grand-Clément & Kroer, arXiv:2202.12277v1, p.9: `ω_{t+1} v_{t+1} ≥_{C°} u_{t+1} − u_t`, i.e.
`ω_{t+1} v_{t+1} − (u_{t+1} − u_t) ∈ C°`, for the CBA+ run.

Formalization Note: `u_t = cbaPlusU …`, `x_t = cbaPlusX …`, `v_t = payoff X (x t) (f t)`,
`C° = target X`.  Stated for every `t ∈ ℕ`: `t = 0` is the first step from `u₀ = 0` (the
corrected start `u₁ = π_C(ω₁ v₁)`), and the paper's `t ≥ 1` are the rest.  No sign condition on
the weights is needed. -/
theorem display_12 {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (x₀ x₁ : E n) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (ω : ℕ → ℝ) (f : ℕ → E n) (t : ℕ) :
    ω (t + 1) • payoff X (cbaPlusX X x₀ x₁ ω f (t + 1)) (f (t + 1)) -
        (cbaPlusU X x₀ x₁ ω f (t + 1) - cbaPlusU X x₀ x₁ ω f t) ∈ target X := by sorry

end ConicBlackwell
