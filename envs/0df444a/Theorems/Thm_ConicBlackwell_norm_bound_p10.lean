-- Prove2me | Theorems.Thm_ConicBlackwell_norm_bound_p10
-- name    : ConicBlackwell.norm_bound_p10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:45:56.104422+00:00
-- url     : https://prove2.me/theorems/dc7378b1-4722-41ff-9a3f-42e4c50fbc84
-- title:
--   Bound $\|u_T\|_2\le\sqrt2\,L\sqrt{\sum_{t\le T}\omega_t^2}$ (p.10) (corrected: factor $\sqrt2$; $u_1$ projected onto $\mathcal C$)
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a nonempty convex compact set, $x_0,x_1\in\mathcal X$, $(\omega_t)$ real weights, $(f_t)$ losses with $\|f_t\|_2\le L$ for $1\le t\le T$, and $(x_t,u_t)$ the CBA$^+$ run with $u_0=0$. Then
--
--   $$
--   \|u_T\|_2\ \le\ \sqrt2\,L\,\sqrt{\sum_{t=1}^T\omega_t^2}.
--   $$
--
--   The page prints $\|u_T\|_2\le L\sqrt{\sum_{t=1}^T\omega_t^2}$, which is false: for $\mathcal X=[-1,1]$, $\omega_1=1$, $x_1=1$, $f_1=1$, $T=1$ one has $u_1=(1,-1)\in\mathcal C$ and $\|u_1\|_2=\sqrt2>1=L$. The factor $\sqrt2$ comes from $\|v_t\|_2^2=\langle f_t,x_t\rangle^2/\kappa^2+\|f_t\|_2^2\le2\|f_t\|_2^2$.
--
--   Differences from the source:
--   - correction: ‖u_T‖₂ ≤ L √(Σ_{t=1}^T ω_t²) → ‖u_T‖₂ ≤ √2 · L · √(Σ_{t=1}^T ω_t²); reason: the printed bound fails for X = [−1, 1], ω₁ = 1, x₁ = 1, f₁ = 1, T = 1: u₁ = (1, −1) ∈ C has norm √2 > 1 = L; the proof's ‖v_t‖₂ ≤ L holds only up to the factor √2
--   - correction: Algorithm 1 line 4: u₁ = ω₁(⟨f₁, x₁⟩/κ, −f₁) (no projection) → u₀ = 0 and u₁ = π_C(ω₁v₁), the UPDATEPAYOFF rule applied to u₀ = 0; reason: the printed u₁ can leave C, contradicting 'we always have u ∈ C' (p.5): X = [−1, 1], x₁ = 1/10, f₁ = 1, f₂ = −1, ω = 1 gives u₁ = (1/10, −1) ∉ C and x₂ = −10 ∉ X; the two agree whenever ω₁v₁ ∈ C
--   - generalization: T ≥ 1, weights ω_t of the run → every T ∈ ℕ (T = 0: u₀ = 0), any real ω; reason: the bound uses no sign of ω
--   - encoding: (4): ‖f‖ ≤ L for every (sub)gradient → ‖f t‖ ≤ L for 1 ≤ t ≤ T; reason: for a single regret minimizer, (4) bounds exactly the observed losses f_1, …, f_T
--   - encoding: ℝⁿ and ℝ × ℝⁿ = ℝⁿ⁺¹ → E n = EuclideanSpace ℝ (Fin n), and lift a x : E (n+1) with the scalar a in coordinate 0; reason: Lean convention of the reused ApproachRegret.ToOLO definitions; same instances (the dimension n = 0 is not excluded; there X ⊆ {0} and the statements stay true)
--   - encoding: κ = max_{x∈X} ‖x‖₂ and v_t = (⟨f_t, x_t⟩/κ, −f_t) → kappa X = sSup of ‖x‖ over X, and payoff X x f = lift (⟪f, x⟫ / kappa X) (−f) with Lean's x/0 = 0; reason: sSup is the max on a nonempty compact X; κ = 0 only when X = {0}, where the page's ⟨f,x⟩/κ is undefined and both coordinates conventions give the same statement
--   - encoding: rounds t ≥ 1 of Algorithm 1 → sequences ℕ → ·, with rounds t ∈ Finset.Icc 1 T; values at index 0 unused (u 0 = 0 is the start of the run); reason: Lean convention; same instances
--   - encoding: π_C(u), the nearest point of C = cone({κ} × X) to u (UPDATEPAYOFF_{CBA+}, p.5) → PerspEpi.projC C u, the unique nearest point if there is one and u otherwise; reason: C is nonempty, closed and convex for nonempty compact convex X (κ > 0: the base {κ} × X is compact and misses 0; κ = 0: X = {0}, C = {0}), so the nearest point exists and is unique and the fallback is never taken
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), proof of Theorem 3.3, p.10, first display ("By definition of L, we conclude that")

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_ConicBlackwell_cbaPlusU
import Definitions.Def_ConicBlackwell_cbaPlusX
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **The bound on `‖u_T‖₂`**, Grand-Clément & Kroer, arXiv:2202.12277v1, p.10, first display, **corrected**:
if `‖f_t‖₂ ≤ L` for `1 ≤ t ≤ T`, then `‖u_T‖₂ ≤ √2 · L · √(Σ_{t=1}^T ω_t²)`.

The page prints `‖u_T‖₂ ≤ L √(Σ_{t=1}^T ω_t²)`, which is false: on `X = [−1, 1]`, `ω = 1`,
`x₁ = 1`, `f₁ = 1`, `T = 1` one gets `u₁ = (1, −1) ∈ C` and `‖u₁‖₂ = √2 > 1`.  The factor `√2`
comes from `‖v_t‖₂² = ⟨f_t, x_t⟩²/κ² + ‖f_t‖₂² ≤ 2‖f_t‖₂²`.

Formalization Note: every `T ∈ ℕ`, every real weights; `u₀ = 0`, `u₁ = π_C(ω₁ v₁)`. -/
theorem norm_bound_p10 {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (x₀ x₁ : E n) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (ω : ℕ → ℝ) (f : ℕ → E n) (L : ℝ) (T : ℕ)
    (hf : ∀ t ∈ Finset.Icc 1 T, ‖f t‖ ≤ L) :
    ‖cbaPlusU X x₀ x₁ ω f T‖ ≤
      Real.sqrt 2 * L * Real.sqrt (∑ t ∈ Finset.Icc 1 T, ω t ^ 2) := by sorry

end ConicBlackwell
