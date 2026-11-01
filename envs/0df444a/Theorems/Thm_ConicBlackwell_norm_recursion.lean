-- Prove2me | Theorems.Thm_ConicBlackwell_norm_recursion
-- name    : ConicBlackwell.norm_recursion
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:45:36.736139+00:00
-- url     : https://prove2.me/theorems/131a4326-337f-4e36-a481-d66d95d167d5
-- title:
--   Telescoped recursion $\|u_t\|_2^2\le\sum_{\tau\le t}\omega_\tau^2\|v_\tau\|_2^2$ (p.9) (corrected: $u_1$ projected onto $\mathcal C$)
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a nonempty convex compact set, $x_0,x_1\in\mathcal X$, $(\omega_t)$ real weights, $(f_t)$ losses, and $(x_t,u_t)$ the CBA$^+$ run with $u_0=0$ and payoffs $v_t=(\langle f_t,x_t\rangle/\kappa,-f_t)$. Then for every $t$
--
--   $$
--   \|u_t\|_2^2\ \le\ \sum_{\tau=1}^t\omega_\tau^2\|v_\tau\|_2^2 .
--   $$
--
--   The squared norm of the aggregate payoff grows at most like the sum of the squared weighted payoffs, with no cross terms.
--
--   Differences from the source:
--   - correction: Algorithm 1 line 4: u₁ = ω₁(⟨f₁, x₁⟩/κ, −f₁) (no projection) → u₀ = 0 and u₁ = π_C(ω₁v₁), the UPDATEPAYOFF rule applied to u₀ = 0; reason: the printed u₁ can leave C, contradicting 'we always have u ∈ C' (p.5): X = [−1, 1], x₁ = 1/10, f₁ = 1, f₂ = −1, ω = 1 gives u₁ = (1/10, −1) ∉ C and x₂ = −10 ∉ X; the two agree whenever ω₁v₁ ∈ C
--   - generalization: t ≥ 1, weights ω_t of the run → every t ∈ ℕ (t = 0: both sides are 0), any real ω; reason: the recursion ‖u_{t+1}‖² ≤ ‖u_t‖² + ω²_{t+1}‖v_{t+1}‖² uses no sign of ω
--   - encoding: ℝⁿ and ℝ × ℝⁿ = ℝⁿ⁺¹ → E n = EuclideanSpace ℝ (Fin n), and lift a x : E (n+1) with the scalar a in coordinate 0; reason: Lean convention of the reused ApproachRegret.ToOLO definitions; same instances (the dimension n = 0 is not excluded; there X ⊆ {0} and the statements stay true)
--   - encoding: κ = max_{x∈X} ‖x‖₂ and v_t = (⟨f_t, x_t⟩/κ, −f_t) → kappa X = sSup of ‖x‖ over X, and payoff X x f = lift (⟪f, x⟫ / kappa X) (−f) with Lean's x/0 = 0; reason: sSup is the max on a nonempty compact X; κ = 0 only when X = {0}, where the page's ⟨f,x⟩/κ is undefined and both coordinates conventions give the same statement
--   - encoding: rounds t ≥ 1 of Algorithm 1 → sequences ℕ → ·, with rounds t ∈ Finset.Icc 1 T; values at index 0 unused (u 0 = 0 is the start of the run); reason: Lean convention; same instances
--   - encoding: π_C(u), the nearest point of C = cone({κ} × X) to u (UPDATEPAYOFF_{CBA+}, p.5) → PerspEpi.projC C u, the unique nearest point if there is one and u otherwise; reason: C is nonempty, closed and convex for nonempty compact convex X (κ > 0: the base {κ} × X is compact and misses 0; κ = 0: X = {0}, C = {0}), so the nearest point exists and is unique and the fallback is never taken
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), proof of Theorem 3.3, p.9 ("By telescoping the inequality above we obtain")

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_ConicBlackwell_cbaPlusU
import Definitions.Def_ConicBlackwell_cbaPlusX
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **The telescoped norm recursion**, Grand-Clément & Kroer, arXiv:2202.12277v1, p.9:
`‖u_t‖₂² ≤ Σ_{τ=1}^t ω_τ² ‖v_τ‖₂²` for the CBA+ run.

Formalization Note: stated for every `t ∈ ℕ` (at `t = 0` both sides are `0`) and every real
weights; `u₀ = 0` and `u₁ = π_C(ω₁ v₁)` (corrected start). -/
theorem norm_recursion {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (x₀ x₁ : E n) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (ω : ℕ → ℝ) (f : ℕ → E n) (t : ℕ) :
    ‖cbaPlusU X x₀ x₁ ω f t‖ ^ 2 ≤
      ∑ τ ∈ Finset.Icc 1 t, ω τ ^ 2 * ‖payoff X (cbaPlusX X x₀ x₁ ω f τ) (f τ)‖ ^ 2 := by sorry

end ConicBlackwell
