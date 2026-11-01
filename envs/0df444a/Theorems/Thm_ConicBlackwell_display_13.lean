-- Prove2me | Theorems.Thm_ConicBlackwell_display_13
-- name    : ConicBlackwell.display_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:45:48.224596+00:00
-- url     : https://prove2.me/theorems/9f62df58-6630-4893-a4e0-263ff1addd30
-- title:
--   Display (13) — $d\big(\sum_t\theta_tv_t,\mathcal C^\circ\big)\le\|(\theta_T/\omega_T)u_T\|_2$ (corrected: $u_1$ projected onto $\mathcal C$)
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a nonempty convex compact set, $x_0,x_1\in\mathcal X$, $(\omega_t)_{t\ge1}$ and $(\theta_t)_{t\ge1}$ positive weights with
--
--   $$
--   \frac{\theta_{t+1}}{\theta_t}\ge\frac{\omega_{t+1}}{\omega_t}\qquad\forall t\ge1,
--   $$
--
--   $(f_t)$ losses, and $(x_t,u_t)$ the CBA$^+$ run with payoff weights $\omega$ and $u_0=0$. Then for every $T\ge1$
--
--   $$
--   d\Big(\sum_{t=1}^T\theta_tv_t,\ \mathcal C^\circ\Big)\ \le\ \Big\|\frac{\theta_T}{\omega_T}u_T\Big\|_2 ,\tag{13}
--   $$
--
--   with $v_t=(\langle f_t,x_t\rangle/\kappa,-f_t)$. It transfers the payoff-weighted aggregate $u_T$ to the decision-weighted payoff sum, which is where the two weight sequences meet.
--
--   Differences from the source:
--   - correction: Algorithm 1 line 4: u₁ = ω₁(⟨f₁, x₁⟩/κ, −f₁) (no projection) → u₀ = 0 and u₁ = π_C(ω₁v₁), the UPDATEPAYOFF rule applied to u₀ = 0; reason: the printed u₁ can leave C, contradicting 'we always have u ∈ C' (p.5): X = [−1, 1], x₁ = 1/10, f₁ = 1, f₂ = −1, ω = 1 gives u₁ = (1/10, −1) ∉ C and x₂ = −10 ∉ X; the two agree whenever ω₁v₁ ∈ C
--   - reading: weights (ω_t), (θ_t) → 0 < ω t and 0 < θ t for t ≥ 1; reason: weights are positive; the ratios θ_{t+1}/θ_t, ω_{t+1}/ω_t and θ_T/ω_T in the statement presuppose it
--   - encoding: ℝⁿ and ℝ × ℝⁿ = ℝⁿ⁺¹ → E n = EuclideanSpace ℝ (Fin n), and lift a x : E (n+1) with the scalar a in coordinate 0; reason: Lean convention of the reused ApproachRegret.ToOLO definitions; same instances (the dimension n = 0 is not excluded; there X ⊆ {0} and the statements stay true)
--   - encoding: κ = max_{x∈X} ‖x‖₂ and v_t = (⟨f_t, x_t⟩/κ, −f_t) → kappa X = sSup of ‖x‖ over X, and payoff X x f = lift (⟪f, x⟫ / kappa X) (−f) with Lean's x/0 = 0; reason: sSup is the max on a nonempty compact X; κ = 0 only when X = {0}, where the page's ⟨f,x⟩/κ is undefined and both coordinates conventions give the same statement
--   - encoding: d(u, S) → Metric.infDist u S; reason: the Euclidean distance to a set
--   - encoding: rounds t ≥ 1 of Algorithm 1 → sequences ℕ → ·, with rounds t ∈ Finset.Icc 1 T; values at index 0 unused (u 0 = 0 is the start of the run); reason: Lean convention; same instances
--   - encoding: π_C(u), the nearest point of C = cone({κ} × X) to u (UPDATEPAYOFF_{CBA+}, p.5) → PerspEpi.projC C u, the unique nearest point if there is one and u otherwise; reason: C is nonempty, closed and convex for nonempty compact convex X (κ > 0: the base {κ} × X is compact and misses 0; κ = 0: X = {0}, C = {0}), so the nearest point exists and is unique and the fallback is never taken
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), proof of Theorem 3.3, display (13), p.9

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_ConicBlackwell_cbaPlusU
import Definitions.Def_ConicBlackwell_cbaPlusX
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **Display (13)**, Grand-Clément & Kroer, arXiv:2202.12277v1, p.9: for the CBA+ run with payoff weights `ω`, decision weights
`θ` and `θ_{t+1}/θ_t ≥ ω_{t+1}/ω_t` for all `t ≥ 1`,
`d(Σ_{t=1}^T θ_t v_t, C°) ≤ ‖(θ_T/ω_T) u_T‖₂`.

Formalization Note: weights are positive (reading of "weights"); `u₀ = 0` and
`u₁ = π_C(ω₁ v₁)` (corrected start, see `cbaPlusState`); `d` is `Metric.infDist`,
`C° = target X`. -/
theorem display_13 {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (x₀ x₁ : E n) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X)
    (ω θ : ℕ → ℝ) (hω : ∀ t, 1 ≤ t → 0 < ω t) (hθ : ∀ t, 1 ≤ t → 0 < θ t)
    (hratio : ∀ t, 1 ≤ t → ω (t + 1) / ω t ≤ θ (t + 1) / θ t)
    (f : ℕ → E n) (T : ℕ) (hT : 1 ≤ T) :
    Metric.infDist
        (∑ t ∈ Finset.Icc 1 T, θ t • payoff X (cbaPlusX X x₀ x₁ ω f t) (f t)) (target X) ≤
      ‖(θ T / ω T) • cbaPlusU X x₀ x₁ ω f T‖ := by sorry

end ConicBlackwell
